mkdir -p evaluation_results/LC
python3 evaluation/leetcode/online.py
mv experiment_result_lc.csv_detailed.csv evaluation_results/LC/tool.csv

mkdir -p evaluation_results/Calcite
python3 evaluation/calcite/online.py
mv experiment_result_calcite.csv evaluation_results/Calcite/tool.csv

mkdir -p evaluation_results/Literature
python3 evaluation/literature/run.py
mv experiment_result_literature.csv evaluation_results/Literature/tool.csv

mkdir -p evaluation_results/D/tool/
python3 evaluation/disambiguation/disambiguation_slabcity_new.py -d 50
mv experiment_result_cubes_disambiguation_50_False.csv evaluation_results/D/tool/experiment_result_cubes_disambiguation_50_False.csv

python3 evaluation/disambiguation/disambiguation_slabcity_new.py -d 100
mv experiment_result_cubes_disambiguation_100_False.csv evaluation_results/D/tool/experiment_result_cubes_disambiguation_100_False.csv

python3 gen_rq1_table.py
