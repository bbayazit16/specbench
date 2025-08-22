import pandas as pd
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
import json
import statistics

from matplotlib.patches import Patch
from matplotlib import patches


matplotlib.rcParams['pdf.fonttype'] = 42
matplotlib.rcParams['ps.fonttype'] = 42
FONT_SIZE = 15

EVAL_RESULTS_DIT = 'evaluation/results/'
lc = pd.read_csv(EVAL_RESULTS_DIT + f'LC/tool.csv')
calcite = pd.read_csv(EVAL_RESULTS_DIT + f'Calcite/tool.csv')
literature = pd.read_csv(EVAL_RESULTS_DIT + f'Literature/tool.csv')

d_50 = pd.read_csv(EVAL_RESULTS_DIT + 'D/tool/experiment_result_cubes_disambiguation_50_False.csv')
d_100 = pd.read_csv(EVAL_RESULTS_DIT + 'D/tool/experiment_result_cubes_disambiguation_100_False.csv')


verieql_d_50 = pd.read_csv(EVAL_RESULTS_DIT + 'D/verieql/experiment_result_cubes_disambiguation_50_False.csv')
verieql_d_100 = pd.read_csv(EVAL_RESULTS_DIT + 'D/verieql/experiment_result_cubes_disambiguation_100_False.csv')


cubes_d_50 = pd.read_csv(EVAL_RESULTS_DIT + 'D/cubes/experiment_result_cubes_disambiguation_50_False.csv')
cubes_d_100 = pd.read_csv(EVAL_RESULTS_DIT + 'D/cubes/experiment_result_cubes_disambiguation_100_False.csv')

datafiller_d_50 = pd.read_csv(EVAL_RESULTS_DIT + 'D/datafiller/experiment_result_cubes_disambiguation_50.csv')
datafiller_d_100 = pd.read_csv(EVAL_RESULTS_DIT + 'D/datafiller/experiment_result_cubes_disambiguation_100.csv')


# Figure 9 (a)

# Data
methods = ['Polygon', 'VeriEQL', 'EvoSQL', 'DataFiller', 'Cosette', 'Qex', 'XData']
values = [5497, 3177, 1824, 134, 17, 14, 1]  # Approximate heights from the image
colors = ['white', 'white', 'white', 'white', 'white', 'white', 'white']
patterns = ['', '', '', '', '', '', '']

# Create figure and axis
# plt.figure(figsize=(10, 6))

# Create bars
fig, ax = plt.subplots(figsize=(6, 4))
for i in range(len(methods)):
    bars = ax.bar(methods[i], values[i], color=colors[i], edgecolor='black', hatch=patterns[i])

    for bar in bars:
        yval = values[i]  # Get the height of each bar
        ax.text(
            bar.get_x() + bar.get_width() / 2,  # x position
            yval,  # y position
            f'{yval}',  # Format the value to two decimal places
            ha='center',  # Horizontal alignment
            va='bottom',  # Vertical alignment
            fontsize=FONT_SIZE  # Adjust fontsize if needed
        )

# Customize bars to match the sketch
# for i, bar in enumerate(bars):
#     if i in [0, 1, 4, 5]:  # Add hatching to match the filled bars in sketch
#         bar.set_hatch('/')

# Customize the plot
ax.set_ylabel('# Benchmarks Solved', fontsize=FONT_SIZE)

# Rotate x-axis labels for better readability
y_ticks = [x * 1000 for x in range(0, 7)]
ax.set_yticks(y_ticks)
# ax.set_yticklabels([f'{tick}' for tick in y_ticks], fontsize=FONT_SIZE)
plt.xticks(rotation=20, ha='right', rotation_mode='anchor')

# Adjust layout to prevent label cutoff

ax.tick_params(axis='y', labelsize=FONT_SIZE)
ax.tick_params(axis='x', labelsize=FONT_SIZE, pad=0, length=5)

# Show the plot
ax.spines['right'].set_visible(False)
ax.spines['top'].set_visible(False)

plt.tight_layout()
plt.savefig('plt/RQ2-Fig-9-a.pdf', format='pdf', transparent=True)


# Figure 9 (b)

# Data for the bar graph
group_labels = ['D-50', 'D-100']  # Two groups
bar_labels = ['Polygon', 'VeriEQL', 'Cubes', 'DataFiller']  # Three bars per group

# Example data for each bar in each group

num_d_50 = len(d_50)
num_d_100 = len(d_100)

values = [[len(d_50[(d_50['?Solved'] == True) & (d_50['Time'] <= 60)]) / num_d_50,  # Time distribution for Group 1, Box 1
           len(verieql_d_50[(verieql_d_50['?Solved'] == True) & (verieql_d_50['Time'] <= 60)]) / num_d_50,  # Time distribution for Group 1, Box 2
           len(cubes_d_50[(cubes_d_50['?Solved'] == True) & (cubes_d_50['Time'] <= 60)]) / num_d_50,
           len(datafiller_d_50[(datafiller_d_50['?Solved'] == True) & (datafiller_d_50['Time'] <= 60)]['Time']) / num_d_50,
           ],
          [len(d_100[(d_100['?Solved'] == True) & (d_100['Time'] <= 60)]) / num_d_100,  # Time distribution for Group 1, Box 1
           len(verieql_d_100[(verieql_d_100['?Solved'] == True) & (verieql_d_100['Time'] <= 60)]) / num_d_100,  # Time distribution for Group 1, Box 2
           len(cubes_d_100[(cubes_d_100['?Solved'] == True) & (cubes_d_100['Time'] <= 60)]) / num_d_100,
           len(datafiller_d_100[(datafiller_d_100['?Solved'] == True) & (datafiller_d_100['Time'] <= 60)]['Time']) / num_d_100,
           ]]  # Each sub-list corresponds to values for one group

# Define the number of groups and bars per group
num_groups = len(group_labels)
num_bars = len(bar_labels)

# Set up bar positions
bar_width = 0.2
x = np.arange(num_groups)  # Group positions

# Define hatch patterns for each bar style
colors = ['black', 'white', 'white', 'white']
patterns = ['', '\\' * 3, '', '.' * 3]  # Use '/' for diagonal stripes, '\' for opposite, and '.' for dots

# Plot each bar in the groups with hatch patterns
fig, ax = plt.subplots(figsize=(6, 4))
for i in range(num_bars):
    # Offset each bar within a group position
    bars = bar = ax.bar(
        x + i * bar_width,
        [values[j][i] for j in range(num_groups)],
        width=bar_width,
        label=bar_labels[i],
        color=colors[i],  # White fill for colorless bars
        edgecolor='black',  # Black edges for visibility
        hatch=patterns[i]  # Apply pattern
    )

    for bar in bars:
        yval = bar.get_height()  # Get the height of each bar
        ax.text(
            bar.get_x() + bar.get_width() / 2,  # x position
            yval,  # y position
            f'{round(yval * 100, 1)}',  # Format the value to two decimal places
            ha='center',  # Horizontal alignment
            va='bottom',  # Vertical alignment
            fontsize='large'  # Adjust fontsize if needed
        )


# Configure the x-axis and legend
ax.set_xticks(x + bar_width)
ax.set_xticklabels(group_labels, fontsize=FONT_SIZE)

# plt.yscale('log')
ticks = [0.2, 0.4, 0.6, 0.8, 1]
ax.set_yticks(ticks)
ax.set_yticklabels([f'{int(tick * 100)}' for tick in ticks], fontsize=FONT_SIZE)
ax.set_ylabel('% Benchmarks Solved', fontsize=FONT_SIZE)

# ax.set_title('Bar Graph with Black and White Patterns')
ax.legend(fontsize=10.5)


# plt.rcParams['figure.figsize'] = [10, 5]

ax.spines['right'].set_visible(False)
ax.spines['top'].set_visible(False)

plt.tight_layout()
plt.savefig('plt/RQ2-Fig-9-b.pdf', format='pdf', transparent=True)


# Fig 10 (a)
np.random.seed(0)  # For reproducibility
tools = ['Polygon', 'VeriEQL', 'EvoSQL', 'DataFiller', 'Cosette', 'Qex', 'XData']
polygon_times = []
polygon_times.append(lc[(lc['?Refuted'] == True) & (lc['Time'] <= 60)]['Time'])
polygon_times.append(calcite[(calcite['?Refuted'] == True) & (calcite['Time'] <= 60)]['Time'])
polygon_times.append(literature[(literature['?Refuted'] == True) & (literature['Time'] <= 60)]['Time'])
polygon_times = pd.concat(polygon_times, axis=0, ignore_index=True)

verieql_time = []
for benchmark in ['LC', 'Calcite', 'Literature']:
    with open(EVAL_RESULTS_DIT + f'{benchmark}/verieql.jsonl') as f:
        for line in f:
            line = json.loads(line)
            if line['states'] is not None and 'NEQ' in line['states'] and line['counterexample'] is not None and sum(sum(line['times'], [])) <= 60:
                verieql_time.append(sum(sum(line['times'], [])))

datafiller_time = []
with open(EVAL_RESULTS_DIT + f'LC/datafiller_time.json') as f:
    f = json.load(f)
    for problem, data in f.items():
        if int(problem[8:-4]) in [619, 595, 175, 182, 511, 577, 584, 596, 1050, 1378, 1587,
                                  512, 183, 613, 1045, 1264, 1350, 1421, 1581, 1693, 1715, 1783,
                                  607, 610, 1083, 1084, 1113, 1141, 1440, 1777, 1747, 1809,
                                  550, 585, 1075, 1097, 1173, 1211, 1251, 1468, 1661,
                                  1789, 1795, 1127, 1435,
                                  603, 614, 1148, 1149, 1364, 1398, 1677, 1731,
                                  ]:
            if data['total'] <= 60:
                datafiller_time.append(data['total'])

data = [polygon_times,
        verieql_time,
        list(filter(lambda x: x <= 60, [120.758, 0.084, 0.034, 0.268, 0.003, 0.104, 0.018, 120.014, 0.015, 0.037,
                                        120.009, 0.011, 0.019, 0.008, 120.057, 120.003, 120.01, 0.008, 120.014, 0.024,
                                        120.015, 0.014, 120.023, 0.043, 0.607, 0.009, 0.272, 0.027, 0.03, 0.003,
                                        0.028, 120.019, 0.014, 0.029, 0.016, 120.015, 1.679, 120.017, 0.131, 120.016,
                                        0.029, 0.018, 1.928, 120.007, 0.003, 0.045, 60.028, 120.009, 120.016, 120.007,
                                        0.015, 120.0, 0.021, 0.011, 0.022])),
        datafiller_time,
        [4.242, 0.175, 0.127, 0.436, 0.213, 0.089, 9.787, 3.813, 8.224, 1.791, 0.088, 8.259, 6.606, 1.697, 33.296, 3.866, 0.075, 1.66, 0.431, 33.121, 6.965, 0.4, 4.006, 2.651, 0.187],
        [2.738, 0.045, 0.135, 0.598, 0.185, 0.42, 84.759, 0.042, 248.676, 0.901, 0.391, 249.373, 2.164, 0.39, 12.137, 87.409, 0.188, 0.383, 0.496, 11.896, 1.534, 0.495, 2.366, 199.514, 0.249],
        [5]
        ]

spacing = 0.6
bar_width = 0.5


fig, ax = plt.subplots(figsize=(6, 4))
for i, d in enumerate(data):
    # Draw each box plot, coloring the first box black
    if len(d) == 0:
        # Draw a red line at the top of the column if data is empty
        ax.plot([i * spacing + 1], [58], 'r_', markersize=25)
    else:
        # color = "black" if i == 0 else "white"
        color = 'white'
        pattern = ''
        bp = ax.boxplot(d, positions=[i * spacing + 1], patch_artist=True, widths=bar_width, boxprops=dict(facecolor=color, hatch=pattern), showfliers=False)
ax.set_xticks([i * spacing + 1 for i in range(len(tools))])
ax.set_xticklabels(tools)
# ax.set_xlabel("Tool")
plt.yscale('log')
y_ticks = [0.01, 0.1, 1, 10, 60]
ax.set_yticks(y_ticks)
ax.set_yticklabels([f'{tick}' for tick in y_ticks], fontsize=FONT_SIZE)
ax.set_ylabel("Time (seconds)", fontsize=FONT_SIZE)

plt.xticks(rotation=20, ha='right', rotation_mode='anchor')

ax.tick_params(axis='y', labelsize=FONT_SIZE)
ax.tick_params(axis='x', labelsize=FONT_SIZE, pad=0, length=5)

ax.spines['right'].set_visible(False)
ax.spines['top'].set_visible(False)

plt.tight_layout()

plt.savefig('plt/RQ2-Fig-10-a.pdf', format='pdf', transparent=True)


# Fig 10 (b)
group1_data = [d_50[(d_50['?Solved'] == True) & (d_50['Time'] <= 60)]['Time'],  # Time distribution for Group 1, Box 1
               verieql_d_50[(verieql_d_50['?Solved'] == True) & (verieql_d_50['Time'] <= 60)]['Time'],  # Time distribution for Group 1, Box 2
               cubes_d_50[(cubes_d_50['?Solved'] == True) & (cubes_d_50['Time'] <= 60)]['Time'],
               datafiller_d_50[(cubes_d_50['?Solved'] == True) & (datafiller_d_50['Time'] <= 60)]['Time'],
               ]  # Time distribution for Group 1, Box 3

group2_data = [d_100[(d_100['?Solved'] == True) & (d_100['Time'] <= 60)]['Time'],  # Time distribution for Group 1, Box 1
               verieql_d_100[(verieql_d_100['?Solved'] == True) & (verieql_d_100['Time'] <= 60)]['Time'],  # Time distribution for Group 1, Box 2
               cubes_d_100[(cubes_d_100['?Solved'] == True) & (cubes_d_100['Time'] <= 60)]['Time'],
               datafiller_d_100[(datafiller_d_100['?Solved'] == True) & (datafiller_d_100['Time'] <= 60)]['Time'],
               ]

fig, ax = plt.subplots(figsize=(6, 4))

# Plot box plots for Group 1 and Group 2
bar_width = 0.4
positions = [1, 1.5, 2, 2.5, 3.5, 4, 4.5, 5]  # Custom positions to space out groups
box_data = group1_data + group2_data  # Combine both groups' data for plotting

# Create box plots
box = ax.boxplot(box_data, positions=positions, widths=bar_width, patch_artist=True, showfliers=False)

# Add labels for each group and style adjustments
ax.set_xticks([1.75, 4.25])  # Central positions for Group 1 and Group 2
ax.set_xticklabels(['D-50', 'D-100'], fontsize=FONT_SIZE)
plt.yscale('log')
y_ticks = [0.5, 1, 2, 5, 10, 30, 60]
ax.set_yticks(y_ticks)
ax.set_yticklabels([f'{tick}' for tick in y_ticks], fontsize=FONT_SIZE)
ax.set_ylabel('Time (seconds)', fontsize=FONT_SIZE)
# ax.set_title('Time Distribution for Two Groups with Three Box Plots Each')

# Add custom colors and style to box plots for clarity
colors = ['black', 'white', 'white', 'white']  # Colorless with black edges for each box
labels = ['Polygon', 'VeriEQL', 'Cubes', 'DataFiller']
patterns = ['', '\\' * 3, '', '.' * 3]  # Patterns for each box plot in groups

# Style each box in box plot
for patch, color, pattern in zip(box['boxes'], colors * 2, patterns * 2):
    patch.set(facecolor=color, hatch=pattern, edgecolor='black')

legend_patches = [Patch(facecolor=color, edgecolor='black', hatch=pattern, label=label) for color, pattern, label in zip(colors, patterns, labels)]
ax.legend(handles=legend_patches, loc='upper left', fontsize=11)

ax.spines['right'].set_visible(False)
ax.spines['top'].set_visible(False)

plt.tight_layout()
plt.savefig('plt/RQ2-Fig-10-b.pdf', format='pdf', transparent=True)
