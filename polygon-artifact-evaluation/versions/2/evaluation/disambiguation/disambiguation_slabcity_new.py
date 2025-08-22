import argparse
import json
import logging
import multiprocessing
import os
import warnings

warnings.simplefilter(action='ignore', category=FutureWarning)

import traceback
from collections import defaultdict

from datetime import datetime

import pandas as pd
from prettytable import PrettyTable

from sql_testing.testers.mysql_tester import MySQLTester
from sql_testing.testers.mysql_tester import DB_CONFIG
from sql_testing.environment import Environment
from sql_testing.logger import logger

BENCHMARK_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'benchmarks')

logger.setLevel(logging.ERROR)

index = {}
for line in open(os.path.join(BENCHMARK_DIR, 'cubes', 'all.jsonlines')):
    line = json.loads(line)
    index[f'{line["id"]}'] = line['schema']


def read_lines_from_directory(directory):
    files_lines_dict = {}  # Dictionary to store file names and their lines
    for filename in os.listdir(directory):
        if filename.endswith('.txt'):
            # Construct full path to the file
            filepath = os.path.join(directory, filename)
            # Open and read lines from the file
            with open(filepath, 'r', encoding='utf-8') as file:
                lines = file.readlines()
                # Remove newline characters
                lines = [line.strip() for line in lines]
            # Add to dictionary, using filename as the key and lines as the value
            files_lines_dict[filename] = lines
    return files_lines_dict


def chunkify(lst, n):
    """Partition a list into n approximately equal-sized chunks."""
    size = len(lst) // n
    remainder = len(lst) % n
    chunks = [lst[i * size + min(i, remainder):(i + 1) * size + min(i + 1, remainder)] for i in range(n)]
    return chunks


def worker(worker_idx, chunk, use_precise_encoding):
    pid = os.getpid()
    num_eq = 0
    num_neq = 0
    num_err = 0
    not_solved = []
    table = PrettyTable([
        'ID', 'Benchmark', '?Solved', 'Counterexample', 'Bound', 'Time',
        '#Iters', '#Backtracking', '%Backtracking Type 2', 'Unsat core sizes', 'M sizes', 'AST size', 'nodes changed'
    ])

    time_budget = 60

    for benchmark in chunk:
        idx, filename, queries = benchmark['id'], benchmark['benchmark'], benchmark['queries']
        # print(filename)
        try:
            schema = json.load(open(os.path.join(BENCHMARK_DIR, 'cubes', 'schema', index[filename.replace('.txt', '').replace('-', '/')])))['Tables']
        except Exception as e:
            # print(e)
            continue

        status = False
        if any('avg' in q.lower() for q in queries):
            bound = 2
            # bound = 3
        elif any('distinct' in q.lower() for q in queries):
            bound = 2
        else:
            bound = 1
            # bound = 2
        # bound = 3
        last_ret = None
        start_time = datetime.now()
        while (datetime.now() - start_time).total_seconds() < time_budget:
            time_left = time_budget - (datetime.now() - start_time).total_seconds()

            try:
                env = Environment(schema, [], bound=bound, time_budget=int(time_left))
                # env = Environment(schema, [], bound=bound, time_budget=time_left)
                eq, cex, checking_time, total_time, ret = env.disambiguate(queries, group_range=0, use_precise_encoding=use_precise_encoding)
                last_ret = ret
                # if eq is None:
                #     break
                if eq is not None and not eq:
                    status = True
                    break
            except Exception as e:
                # print('ERROR', ''.join(traceback.format_tb(e.__traceback__)) + str(e))
                status = None
                break

            bound += 1

        if status is None:
            # print(filename, 'err')
            table.add_row((
                idx, filename, 'ERR', None, None,
                None, None, None, None, None, None, None, None
            ))
            num_err += 1
        elif status:
            print(idx, filename, 'solved')

            try:
                tester = MySQLTester(DB_CONFIG, schema, db_predix=f'testing_disambiguation_{worker_idx}')
                tester.create_test_database(cex, [])
                cluster = tester.test_cluster(queries)
                if 'query_not_executable' not in list(cluster.keys()) and len(cluster) == 1:
                    # or list(cluster.values())[0] - list(cluster.values())[1] != 0
                    table.add_row((
                        idx, filename, False, None, bound, total_time,
                        last_ret['iters'], last_ret['backtracks'],
                        last_ret['type_2_backtracks'] / last_ret['backtracks'] if last_ret['backtracks'] > 0 else None,
                        last_ret['unsat_core_sizes'],
                        last_ret['M_sizes'],
                        last_ret['ast_size'],
                        last_ret['num_nodes_changed']
                    ))
                    num_eq += 1
                else:
                    table.add_row((
                        idx, filename, True, cex, bound, total_time,
                        last_ret['iters'], last_ret['backtracks'],
                        last_ret['type_2_backtracks'] / last_ret['backtracks'] if last_ret['backtracks'] > 0 else None,
                        last_ret['unsat_core_sizes'],
                        last_ret['M_sizes'],
                        last_ret['ast_size'],
                        last_ret['num_nodes_changed']
                    ))
                    num_neq += 1
                    # print('succ', str(cluster))
            except Exception as e:
                table.add_row((
                    idx, filename, True, cex, bound, total_time,
                    last_ret['iters'], last_ret['backtracks'],
                    last_ret['type_2_backtracks'] / last_ret['backtracks'] if last_ret['backtracks'] > 0 else None,
                    last_ret['unsat_core_sizes'],
                    last_ret['M_sizes'],
                    last_ret['ast_size'],
                    last_ret['num_nodes_changed']
                ))
                num_neq += 1
                # print('ERROR', ''.join(traceback.format_tb(e.__traceback__)) + str(e))
        else:
            print(idx, filename)
            table.add_row((
                idx, filename, False, None, bound, total_time, None, None, None, None, None, None, None
            ))
            not_solved.append(idx)
            num_eq += 1

    with open(f'experiment_result_cubes_disambiguation_{worker_idx}.csv', 'w', newline='') as f:
        f.write(table.get_csv_string())

    return pid, not_solved, num_eq, num_neq, num_err


def main(num_queries, use_precise_encoding, subset):
    not_solved = []

    num_eq = 0
    num_err = 0
    num_neq = 0

    count = 0

    NUM_PROCESSES = max(os.cpu_count() // 2, 1)

    pool = multiprocessing.Pool(processes=NUM_PROCESSES)

    all_benchmarks = []
    with open(os.path.join(BENCHMARK_DIR, 'cubes', f'benchmarks_{num_queries}_extended.jsonl'), 'r') as file:
        for benchmark in file:
            count += 1
            benchmark = json.loads(benchmark)

            if subset:
                if benchmark['id'] < 20 or benchmark['id'] >= 30:
                    continue

            all_benchmarks.append(benchmark)

    print(len(all_benchmarks))
    results = []
    for idx, chunk in enumerate(chunkify(all_benchmarks, NUM_PROCESSES)):
        results.append(pool.apply_async(worker, args=(idx, chunk, use_precise_encoding)))

    pool.close()
    pool.join()

    pids = []
    for result in results:
        pid, p_not_solved, p_num_eq, p_num_neq, p_num_err = result.get()
        pids.append(pid)
        not_solved.extend(p_not_solved)
        num_eq += p_num_eq
        num_neq += p_num_neq
        num_err += p_num_err

    print('solved:', num_neq)
    print('not solved:', num_eq)
    print('err:', num_err)

    csv_files = [f'experiment_result_cubes_disambiguation_{worker_idx}.csv' for worker_idx in range(NUM_PROCESSES)]
    first_csv = pd.read_csv(csv_files[0])
    header = list(first_csv.columns)

    combined_data = pd.DataFrame(columns=header)

    for csv_file in csv_files:
        data = pd.read_csv(csv_file)
        combined_data = pd.concat([combined_data, data], ignore_index=True)

    combined_data.to_csv(f'experiment_result_cubes_disambiguation_{num_queries}_{use_precise_encoding}.csv', index=False)

    for csv_file in csv_files:
        os.remove(csv_file)

    for pid in pids:
        os.system(f'pkill -9 -P {pid}')
        os.system(f'pkill -9 -g {pid}')
        os.system(f'pkill -9 -G {pid}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()

    parser.add_argument('-d', type=int, required=True)
    parser.add_argument('--subset', action='store_true')

    args = parser.parse_args()
    print(args)

    main(args.d, False, args.subset)
