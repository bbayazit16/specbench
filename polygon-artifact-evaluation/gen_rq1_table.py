import ast
import statistics
from collections import defaultdict

import pandas as pd
import warnings
warnings.filterwarnings("ignore")


EVAL_RESULTS_DIT = 'evaluation_results/'

print('benchmark,solved,'
      'nodes_avg,nodes_med,nodes_max,'
      'time_avg,time_med,'
      'num_iters_avg,num_iters_med,num_iters_max,'
      'num_resolve_conflict_avg,num_resolve_conflict_med,num_resolve_conflict_max,'
      'adjusted_avg,adjusted_med,adjusted_max'
      )

# Equivalence Checking
solved = 0
columns = defaultdict(list)

## LC
df = pd.read_csv(EVAL_RESULTS_DIT + f'LC/tool.csv')
df = df[(df['?Refuted'] == True) & (df['Time'] <= 60)]
solved += len(df)
columns['#Iters'].append(df['#Iters'])
columns['Time'].append(df['Time'])
columns['AST size'].append(df['AST size'])
columns['#Backtracking'].append(df['#Backtracking'])
for adjusted in df['nodes changed']:
    try:
        nums = ast.literal_eval(adjusted)
        columns['adjusted'].append(pd.DataFrame(nums, columns=['adjusted'])['adjusted'])
    except Exception as e:
        print(e)
        pass

## Calcite
try:
    df = pd.read_csv(EVAL_RESULTS_DIT + f'Calcite/tool.csv')
    df = df[(df['?Refuted'] == True) & (df['Time'] <= 60)]
    solved += len(df)
    columns['#Iters'].append(df['#Iters'])
    columns['Time'].append(df['Time'])
    columns['AST size'].append(df['AST size'])
    columns['#Backtracking'].append(df['#Backtracking'])
    for adjusted in df['nodes changed']:
        try:
            nums = ast.literal_eval(adjusted)
            columns['adjusted'].append(pd.DataFrame(nums, columns=['adjusted'])['adjusted'])
        except Exception as e:
            print(e)
            pass
except:
    pass

## Literature
try:
    df = pd.read_csv(EVAL_RESULTS_DIT + f'Literature/tool.csv')
    df = df[(df['?Refuted'] == True) & (df['Time'] <= 60)]
    solved += len(df)
    columns['#Iters'].append(df['#Iters'])
    columns['Time'].append(df['Time'])
    columns['AST size'].append(df['AST size'])
    columns['#Backtracking'].append(df['#Backtracking'])
    for adjusted in df['nodes changed']:
        try:
            nums = ast.literal_eval(adjusted)
            columns['adjusted'].append(pd.DataFrame(nums, columns=['adjusted'])['adjusted'])
        except Exception as e:
            print(e)
            pass
except:
    pass

## Summary
print(f'ER,{solved}', end='')
for column in ['AST size', 'Time', '#Iters', '#Backtracking', 'adjusted']:
    mean_value = pd.concat(columns[column], axis=0, ignore_index=True).mean()
    q2 = pd.concat(columns[column], axis=0, ignore_index=True).median()
    max_value = pd.concat(columns[column], axis=0, ignore_index=True).max()

    if column in ['AST size', 'adjusted']:
        mean_value = round(mean_value)
        q2 = round(q2)
        max_value = round(max_value)
    else:
        mean_value = round(mean_value, 1)
        q2 = round(q2, 1)
        max_value = round(max_value)

    if column == 'Time':
        print(f',{mean_value},{q2}', end='')
    else:
        print(f',{mean_value},{q2},{max_value}', end='')

print()

# Disambiguation
for d in [50, 100]:
    df = pd.read_csv(EVAL_RESULTS_DIT + f'D/tool/experiment_result_cubes_disambiguation_{d}_False.csv')
    total = len(df)
    df = df[(df['?Solved'] == True) & (df['Time'] <= 60)]

    solved = len(df)

    print(f'D-{d},{solved}', end='')

    for column in ['AST size', 'Time', '#Iters', '#Backtracking']:
        mean_value = df[column].mean()
        q2 = df[column].median()
        max_value = df[column].max()

        if column == 'AST size':
            mean_value = round(mean_value)
            q2 = round(q2)
            max_value = round(max_value)
        else:
            mean_value = "{:.2f}".format(mean_value)
            q2 = round(q2, 1)
            max_value = round(max_value, 1)

        if column == 'Time':
            print(f',{mean_value},{q2}', end='')
        else:
            print(f',{mean_value},{q2},{max_value}', end='')

    nums = []
    for s in df['nodes changed']:
        try:
            sizes = ast.literal_eval(s)
            nums.extend(sizes)
        except Exception as e:
            print(e)
            pass
    print(f',{round(statistics.mean(nums))},{round(statistics.median(nums))},{round(max(nums))}',end='')
    print()
