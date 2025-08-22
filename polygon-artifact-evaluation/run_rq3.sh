
for version in 1.1 1.2 1.3 1.4 1.5 2 3 4 4.2 5; do

    echo Start ablation $version

    cp -rf versions/$version/* .

    mkdir -p evaluation_results/LC
    python3 evaluation/leetcode/online.py
    mv experiment_result_lc.csv_detailed.csv evaluation_results/LC/$version.csv

    mkdir -p evaluation_results/D/$version/
    python3 evaluation/disambiguation/disambiguation_slabcity_new.py -d 50
    mv experiment_result_cubes_disambiguation_50_False.csv evaluation_results/D/$version/experiment_result_cubes_disambiguation_50_False.csv

    python3 evaluation/disambiguation/disambiguation_slabcity_new.py -d 100
    mv experiment_result_cubes_disambiguation_100_False.csv evaluation_results/D/$version/experiment_result_cubes_disambiguation_100_False.csv

done

cp -rf versions/tool/* .

mkdir -p plt
python3 rq3.py
