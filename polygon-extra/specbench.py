#!/usr/bin/env python3

import os
from pathlib import Path
import ujson
import pandas as pd
import traceback
from llm import call_llm
from models import LLM, DefaultLLM, OpenAIReasoning
from sql_testing.constraint_parser import ConstraintParser
from sql_testing.environment import Environment
from evaluation.calcite.tester import MySQLTester

BENCHMARK_DIR = os.path.join(os.path.dirname(__file__), 'benchmarks')

def check(problem_id, user_query, verify_with_mysql=False, db_config=None):    
    benchmark_dir = os.path.join(BENCHMARK_DIR, 'leetcode')
    
    try:
        schema = ujson.load(open(f'{benchmark_dir}/schemas/{problem_id}.json'))
        groundtruths = pd.read_csv(f'{benchmark_dir}/groundtruths/{problem_id}.csv')
        ground_truth = groundtruths['mysql_groundtruth'][0]
        # print('ground_truth')
        # print(ground_truth)
        
        constraint_parser = ConstraintParser()
        constraints = constraint_parser.parse_from_file(f"{benchmark_dir}/constraints/{problem_id}.yml")
        
        bound = 2
        if problem_id in [619, 1050, 1398]:
            bound = 3
        elif problem_id in [1661]:
            bound = 4
        elif problem_id in [596, 1149]:
            bound = 5
        # elif problem_id in {607, 183, 619, 1084, 1251, 585}:
        #     bound = 100
            
        default_k = {
            'filter': 4,
            'project': 4,
            'union': 4,
            'inner join': 4,
            'left join': 4,
            'right join': 4,
            'full join': 4,
            'product': 4,
            'order by': 2
        }
        
        env = Environment(schema['Tables'], constraints, bound=bound, default_k=default_k, time_budget=60)
        
        eq, cex, checking_time, total_time, ret = env.check(ground_truth, user_query)
        
        mysql_verified = None
        if verify_with_mysql and eq is False and cex is not None:
            try:
                if db_config is None:
                    db_config = {'host': 'localhost', 'user': 'root', 'password': 'pinhan'}
                
                with MySQLTester(db_config, schema['Tables'], db_predix=f'specbench_{problem_id}') as tester:
                    tester.create_all_databases([cex], constraints)
                    mysql_verified = tester.test_pair(ground_truth, user_query)
            except Exception as mysql_error:
                mysql_verified = None
        
        result = {
            'equivalent': eq,
            'counterexample': cex,
            'time': total_time,
            'mysql_verified': mysql_verified,
            'details': {
                'iterations': ret.get('iters'),
                'backtracks': ret.get('backtracks'),
                'ast_size': ret.get('ast_size'),
                'unsat_core_sizes': ret.get('unsat_core_sizes'),
                'solving_times': ret.get('solving_time_per_iter'),
                'nodes_changed': ret.get('num_nodes_changed')
            }
        }
        
        return result
        
    except Exception as e:
        return {
            'equivalent': None,
            'counterexample': None,
            'time': None,
            'mysql_verified': None,
            'details': None,
            'error': str(e),
            'traceback': traceback.format_exc()
        }
    

def call_llm_logged(question_id: str, prompt: str, model: LLM) -> str:
    p = Path('logs') / model.display_name()
    p.mkdir(exist_ok=True, parents=True)

    look_for = (p / question_id).with_suffix('.log')
    if look_for.exists():
        return look_for.read_text().strip()
    else:
        result = call_llm(prompt, model, 10_000, 0.0)
        with open(look_for, 'w+') as f:
            f.write(result)
        return result

# llm = DefaultLLM('google/gemma-3-4b-it')
# llm = OpenAIReasoning('openai/gpt-5-chat', 'high')
# llm = DefaultLLM('openai/gpt-5')
# llm = DefaultLLM('openai/gpt-5-mini')
# llm = DefaultLLM('openai/gpt-5-nano')
# llm = DefaultLLM('qwen/qwen3-30b-a3b-instruct-2507')
llm = DefaultLLM('google/gemma-3-4b-it')

if __name__ == '__main__':
    with open('lc_info.json', 'r') as f:
        j: dict = ujson.load(f)

    total = 0
    total_success = 0
    total_unknown = 0
    for question_id, question in j.items():
        # if question_id != '619': continue 
        prompt = question['html']
        if not prompt:
            continue

        total += 1

        slug = question['slug']
        
        print('Calling LLM for', question_id, ':', f'https://leetcode.com/problems/{slug}')
        sql_result = call_llm_logged(question_id, prompt, llm)
        print('result:')
        print(sql_result)
        print('Received LLM response, running polygon')
        result_info = check(question_id, sql_result)
        equivalent = result_info['equivalent']

        if equivalent:
            print('Result: Success!')
            total_success += 1
        elif equivalent is None:
            total_unknown += 1
            print('Result: Unknown!')
            print(result_info)
        else:
            print(f"Counterexample: {result_info['counterexample']}")
        # if result_info['counterexample']:

        if result_info.get('error'):
            print(f"Error: {result_info['error']}")
            
        print()

    print('Total:', total)
    print('Total success:', total_success)
    print('Total unknown', total_unknown)
