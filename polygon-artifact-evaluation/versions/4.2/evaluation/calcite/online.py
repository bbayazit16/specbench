import logging
import os
import ujson
from datetime import datetime

from prettytable import PrettyTable

from sql_testing.constraint_parser import ConstraintParser
from sql_testing.environment import Environment
from sql_testing.logger import logger
from evaluation.calcite.tester import MySQLTester

BENCHMARK_DIR = os.path.join(os.path.dirname(__file__), '..', '..', 'benchmarks')
MYSQL_DB_CONFIG = {'host': 'localhost', 'user': 'root', 'password': 'pinhan'}
PSQL_DB_CONFIG = {'host': 'localhost', 'user': 'postgres', 'password': 'pinhan'}

logger.level = logging.DEBUG


def calcite(bound=2):
    output_file_name = 'experiment_result_calcite.csv'

    logger.info('experiment started')

    benchmark_dir = os.path.join(BENCHMARK_DIR, 'calcite')
    schema = ujson.load(open(f'{benchmark_dir}/schema.json'))
    benchmarks = open(f'{benchmark_dir}/calcite2.jsonlines')
    constraint_parser = ConstraintParser()
    constraints = constraint_parser.parse_from_file(f"{benchmark_dir}/constraints.yml")

    table = PrettyTable([
        'ID', '?Refuted', 'Time', 'Counterexample',
        '#Iters', '#Backtracking', '%Backtracking Type 2', 'Unsat core sizes', 'M sizes', 'solving times', 'AST size', 'nodes changed'
    ])

    for line in benchmarks:
        line = ujson.loads(line)
        try:
            if line['index'] not in [13, 166, 245, 326]:
                continue

            env = Environment(schema['Tables'], constraints, bound=bound, time_budget=60)
            eq, cex, checking_time, total_time, ret = env.check(*line['pair'], use_precise_encoding=False)

            if eq is not None:
                if not eq:
                    print(cex)
                    with MySQLTester(MYSQL_DB_CONFIG, schema['Tables']) as tester:
                        tester.create_all_databases([cex], constraints)
                        rejected = tester.test_pair(line['pair'][0], line['pair'][1])
                    table.add_row((line['index'], True, total_time, cex,
                                   ret['iters'], ret['backtracks'],
                                   ret['type_2_backtracks'] / ret['backtracks'] if ret['backtracks'] > 0 else None,
                                   ret['unsat_core_sizes'],
                                   ret['M_sizes'],
                                   str(ret['solving_time_per_iter']),
                                   ret['ast_size'],
                                   ret['num_nodes_changed']
                                   ))
                    if rejected:
                        logger.critical(line['index'])
                else:
                    logger.info(line['index'])
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
                table.add_row((line['index'], False, None, None,
                               None, None,
                               None, None, None, None,
                               None, None
                               ))
        except:
            table.add_row((line['index'], False, None, None,
                           None, None,
                           None, None, None, None,
                           None, None
                           ))
            continue

    with open(output_file_name, 'w', newline='') as f:
        f.write(table.get_csv_string())


if __name__ == '__main__':
    calcite()
