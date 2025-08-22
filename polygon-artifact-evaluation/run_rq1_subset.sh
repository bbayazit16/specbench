mkdir -p evaluation_results/LC
python3 evaluation/leetcode/online.py --subset
mv experiment_result_lc.csv_detailed.csv evaluation_results/LC/tool.csv

mkdir -p evaluation_results/D/tool/
python3 evaluation/disambiguation/disambiguation_slabcity_new.py -d 50 --subset
mv experiment_result_cubes_disambiguation_50_False.csv evaluation_results/D/tool/experiment_result_cubes_disambiguation_50_False.csv

python3 evaluation/disambiguation/disambiguation_slabcity_new.py -d 100 --subset
mv experiment_result_cubes_disambiguation_100_False.csv evaluation_results/D/tool/experiment_result_cubes_disambiguation_100_False.csv

python3 gen_rq1_table.py
