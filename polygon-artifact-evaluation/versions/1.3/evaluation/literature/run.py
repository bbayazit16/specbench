import logging
import math
import os
import re

import ujson
import pandas as pd
from collections import defaultdict
from datetime import datetime

from iteration_utilities import unique_everseen
from prettytable import PrettyTable

from sql_testing.environment import Environment
from sql_testing.logger import logger
from evaluation.calcite.tester import MySQLTester

BENCHMARK_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'benchmarks')
DB_CONFIG = {'host': 'localhost', 'user': 'root', 'password': 'pinhan'}

logger.level = logging.INFO


def literature(bound=3):
    benchmark_dir = os.path.join(BENCHMARK_DIR, 'literature')

    benchmarks = open(f'{benchmark_dir}/literature-rewrite.jsonlines')

    output_file_name = f'experiment_result_literature.csv'

    total = 0
    killed = 0

    table = PrettyTable([
        'ID', '?Refuted', 'Time', 'Counterexample',
        '#Iters', '#Backtracking', '%Backtracking Type 2', 'Unsat core sizes', 'M sizes', 'solving times',
        'AST size', 'nodes changed'
    ])

    for line in benchmarks:
        total += 1
        line = ujson.loads(line)

        schema = ujson.load(open(f'{benchmark_dir}/schemas/{line["benchmark"]}.json'))

        k = 4
        # k = 99
        # pattern = r'(?i)count\(.*?\)\s*(>=|>)\s*(\d+)'
        # matches = re.findall(pattern, ' '.join(line['pair']))
        # for op, num in matches:
        #     num = int(num)
        #     if op == '>':
        #         k = num + 1
        #     else:
        #         k = num
        #
        # if k > 9:
        #     bound = math.ceil(math.sqrt(k))
        try:
            env = Environment(schema['Tables'], [], bound=bound, time_budget=60)
            eq, cex, checking_time, total_time, ret = env.check(*line['pair'], use_precise_encoding=False)

            if eq is not None:
                if not eq:
                    with MySQLTester(DB_CONFIG, schema['Tables']) as tester:
                        tester.create_all_databases([cex], [])
                        rejected = tester.test_pair(line['pair'][0], line['pair'][1])
                    if rejected:
                        killed += 1
                        logger.critical(line['index'])
                        table.add_row((line['index'], True, total_time, cex,
                                       ret['iters'], ret['backtracks'],
                                       ret['type_2_backtracks'] / ret['backtracks'] if ret['backtracks'] > 0 else None,
                                       ret['unsat_core_sizes'],
                                       ret['M_sizes'],
                                       str(ret['solving_time_per_iter']),
                                       ret['ast_size'],
                                       ret['num_nodes_changed']
                                       ))
                    else:
                        table.add_row((line['index'], False, total_time, cex,
                                       ret['iters'], ret['backtracks'],
                                       ret['type_2_backtracks'] / ret['backtracks'] if ret['backtracks'] > 0 else None,
                                       ret['unsat_core_sizes'],
                                       ret['M_sizes'],
                                       str(ret['solving_time_per_iter']),
                                       ret['ast_size'],
                                       ret['num_nodes_changed']
                                       ))
                else:
                    table.add_row((line['index'], False, total_time, cex,
                                   ret['iters'], ret['backtracks'],
                                   ret['type_2_backtracks'] / ret['backtracks'] if ret['backtracks'] > 0 else None,
                                   ret['unsat_core_sizes'],
                                   ret['M_sizes'],
                                   str(ret['solving_time_per_iter']),
                                   ret['ast_size'],
                                   ret['num_nodes_changed']
                                   ))
                    logger.info(line['index'])
            else:
                table.add_row((line['index'], False, None, None,
                               None, None,
                               None, None, None, None, None, None
                               ))
        except Exception as e:
            print(e)
            table.add_row((line['index'], False, None, None,
                           None, None,
                           None, None, None, None, None, None
                           ))

    print(total, killed)

    with open(output_file_name, 'w', newline='') as f:
        f.write(table.get_csv_string())
    logger.info('done')


if __name__ == '__main__':
    literature()
