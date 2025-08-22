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

EVAL_RESULTS_DIT = 'evaluation_results/'
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


# Figure 11 (a)

# Data
methods = ['Polygon', 'Enum-TopUAs', 'Enum-75%Top', 'Enum-50%Top', 'Enum-25%Top', 'Enum-MinUAs', 'TopUACover', 'MinUAsCover', 'NoNewConflicts', 'NoUnsatCore', 'AddMinUAs']
values = []
for tool in ['tool', '1.5', '1.4', '1.3', '1.2', '1.1', '4', '4.2', '3', '2', '5']:
    solved = 0
    for benchmark in ['LC', 'Calcite', 'Literature']:
        df = pd.read_csv(EVAL_RESULTS_DIT + f'{benchmark}/{tool}.csv')
        df = df[(df['?Refuted'] == True) & (df['Time'] <= 60)]
        solved += len(df)
    values.append(solved)

colors = ['black', 'white', 'white', 'white', 'white', 'white', 'white', 'white', 'white', 'white', 'white']
patterns = ['', '\\' * 3, '\\' * 3, '\\' * 3, '\\' * 3, '\\' * 3, '', '', '', '', '']

# Create figure and axis
# plt.figure(figsize=(10, 6))

# Create bars
fig, ax = plt.subplots(figsize=(6, 5))
for i in range(len(methods)):
    bars = ax.bar(methods[i], values[i], width=0.7, color=colors[i], edgecolor='black', hatch=patterns[i])

    for bar in bars:
        yval = values[i]  # Get the height of each bar
        ax.text(
            bar.get_x() + bar.get_width() / 2,  # x position
            yval,  # y position
            f'{yval}',  # Format the value to two decimal places
            ha='center',  # Horizontal alignment
            va='bottom',  # Vertical alignment
            fontsize=11  # Adjust fontsize if needed
        )

# Customize bars to match the sketch
# for i, bar in enumerate(bars):
#     if i in [0, 1, 4, 5]:  # Add hatching to match the filled bars in sketch
#         bar.set_hatch('/')

# Customize the plot
y_ticks = [x * 1000 for x in range(0, 7)]
ax.set_yticks(y_ticks)
ax.set_ylabel('# Benchmarks Solved', fontsize=FONT_SIZE + 3)

# Rotate x-axis labels for better readability
plt.xticks(rotation=40, ha='right', rotation_mode='anchor')

# Adjust layout to prevent label cutoff

ax.tick_params(axis='y', labelsize=FONT_SIZE + 2)
ax.tick_params(axis='x', labelsize=FONT_SIZE + 2, pad=-2, length=5)

# Show the plot
ax.spines['right'].set_visible(False)
ax.spines['top'].set_visible(False)

plt.tight_layout()
plt.savefig('plt/RQ3-Fig-11-a.pdf', format='pdf', transparent=True)


# Figure 11 (b)

# Data for the bar graph
group_labels = ['D-50', 'D-100']  # Two groups
bar_labels = ['Polygon', 'Enum-TopUAs', 'Enum-75%Top', 'Enum-50%Top', 'Enum-25%Top', 'Enum-MinUAs', 'TopUACover', 'MinUAsCover', 'NoNewConflicts', 'NoUnsatCore', 'AddMinUAs']

values = []
# Example data for each bar in each group
for d in [50, 100]:
    d_values = []
    for setup in ['tool', '1.5', '1.4', '1.3', '1.2', '1.1', '4', '4.2', '3', '2', '5']:
        df = pd.read_csv(EVAL_RESULTS_DIT + f'D/{setup}/experiment_result_cubes_disambiguation_{d}_False.csv')
        total = len(df)
        df = df[(df['?Solved'] == True) & (df['Time'] <= 60)]
        d_values.append(len(df) / total)
    values.append(d_values)
# Define the number of groups and bars per group
num_groups = len(group_labels)
num_bars = len(bar_labels)

# Set up bar positions
# bar_width = 0.1
group_width = 0.9  # Total width for each group
bar_width = group_width / num_bars * 0.8  # Make bars slightly narrower to create gaps
gap_between_bars = bar_width * 0.3  # Small gap between bars within a group
x = np.arange(num_groups)  # Group positions

# Define hatch patterns for each bar style
patterns = ['']  * len(bar_labels)  # Use '/' for diagonal stripes, '\' for opposite, and '.' for dots

# Plot each bar in the groups with hatch patterns
fig, ax = plt.subplots(figsize=(14, 7))
bar_positions_all = []
for i in range(num_bars):
    # Offset each bar within a group position
    bar_center = (i - (num_bars - 1)/2) * (bar_width + gap_between_bars)
    bar_positions = x + bar_center
    color = 'black' if i == 0 else 'white'
    # color = 'white'
    pattern = '' if i > 5 else '\\' * 3
    bars = ax.bar(
        # x + i * bar_width,
        bar_positions,
        [values[j][i] for j in range(num_groups)],
        width=bar_width,
        label=bar_labels[i],
        color=color,  # White fill for colorless bars
        edgecolor='black',  # Black edges for visibility
        hatch=pattern  # Apply pattern
    )

    for bar in bars:
        yval = bar.get_height()  # Get the height of each bar
        ax.text(
            bar.get_x() + bar.get_width() / 2,  # x position
            yval,  # y position
            f'{round(yval * 100)}',  # Format the value to two decimal places
            ha='center',  # Horizontal alignment
            va='bottom',  # Vertical alignment
            fontsize=18  # Adjust fontsize if needed
        )

        bar_positions_all.append(bar.get_x() + bar.get_width() / 2)

    # for j, pos in enumerate(bar_positions):
    #     ax.text(pos,
    #             -0.08,
    #             bar_labels[i],
    #             ha='right',  # Changed from 'center' to 'right'
    #             va='top',
    #             rotation=45,
    #             rotation_mode='anchor')

for group_x in x[:-1]:
    ax.axvline(x=group_x + group_width/2 + 0.05,
               color='black',
               linestyle=':',
               linewidth=3,
               alpha=.6)

for i, pos in enumerate(x + bar_width):
    ax.text(pos,
            1.05,
            group_labels[i],
            ha='right',  # Changed from 'center' to 'right'
            va='top',
            fontsize=FONT_SIZE + 6
            )

# Configure the x-axis and legend
# ax.set_xticks(x + bar_width)
ax.set_xticks(sorted([p for p in bar_positions_all]))
ax.set_xticklabels([*bar_labels, *bar_labels])
plt.xticks(rotation=38, ha='right', rotation_mode='anchor')
ax.tick_params(axis='x', labelsize=FONT_SIZE + 5, pad=-2, length=5)

# ax.set_xticklabels(group_labels)
# plt.yscale('log')
ax.set_ylim(0, 1)
ticks = [0, 0.2, 0.4, 0.6, 0.8, 1]
ax.set_yticks(ticks)
ax.set_yticklabels([f'{int(tick * 100)}' for tick in ticks], fontsize=FONT_SIZE + 6)
ax.set_ylabel('% Benchmarks Solved', fontsize=FONT_SIZE + 6)
# ax.set_title('Bar Graph with Black and White Patterns')
# ax.legend()

ax.spines['right'].set_visible(False)
ax.spines['top'].set_visible(False)

plt.tight_layout()

plt.savefig('plt/RQ3-Fig-11-b.pdf', format='pdf', transparent=True)


# Figure 12 (a)

tools = ['Polygon', 'Enum-TopUAs', 'Enum-75%Top', 'Enum-50%Top', 'Enum-25%Top', 'Enum-MinUAs', 'TopUACover', 'MinUAsCover', 'NoNewConflicts', 'NoUnsatCore', 'AddMinUAs']
data = []
for tool in ['tool', '1.5', '1.4', '1.3', '1.2', '1.1', '4', '4.2', '3', '2', '5']:
    solved = 0
    times = []
    for benchmark in ['LC', 'Calcite', 'Literature']:
        df = pd.read_csv(EVAL_RESULTS_DIT + f'{benchmark}/{tool}.csv')
        df = df[(df['?Refuted'] == True) & (df['Time'] <= 60) & (df['Time'] > 0)]
        times.append(df['Time'])
    data.append(pd.concat(times, axis=0, ignore_index=True))

bar_width = 0.48

fig, ax = plt.subplots(figsize=(6, 5))
for i, d in enumerate(data):
    # Draw each box plot, coloring the first box black
    if len(d) == 0:
        # Draw a red line at the top of the column if data is empty
        ax.plot([i + 1], [58], 'r_', markersize=25)
    else:
        color = "black" if i == 0 else "white"
        pattern = '' if i > 5 else '\\' * 3
        bp = ax.boxplot(d, positions=[i * 0.7], patch_artist=True, widths=bar_width, boxprops=dict(facecolor=color, hatch=pattern), showfliers=False)
ax.set_xticks([i * 0.7 for i in range(0, len(tools))])
ax.set_xticklabels(tools)
# ax.set_xlabel("Tool")
plt.yscale('log')
ax.set_ylabel("Time (seconds)", fontsize=FONT_SIZE + 3)
# ax.set_ylim(0, 10)

plt.xticks(rotation=40, ha='right', rotation_mode='anchor')

ax.tick_params(axis='y', labelsize=FONT_SIZE + 2)
ax.tick_params(axis='x', labelsize=FONT_SIZE + 2, pad=-2, length=5)

ax.spines['right'].set_visible(False)
ax.spines['top'].set_visible(False)

plt.tight_layout()

plt.savefig('plt/RQ3-Fig-12-a.pdf', format='pdf', transparent=True)



# Figure 12 (b)

# Data preparation
labels = ['Polygon', 'Enum-TopUAs', 'Enum-75%Top', 'Enum-50%Top', 'Enum-25%Top', 'Enum-MinUAs', 'TopUACover',
          'MinUAsCover', 'NoNewConflicts', 'NoUnsatCore', 'AddMinUAs']

box_data = []
for d in [50, 100]:
    d_values = []
    for setup in ['tool', '1.5', '1.4', '1.3', '1.2', '1.1', '4', '4.2', '3', '2', '5']:
        df = pd.read_csv(EVAL_RESULTS_DIT + f'D/{setup}/experiment_result_cubes_disambiguation_{d}_False.csv')
        df = df[(df['?Solved'] == True) & (df['Time'] <= 60) & (df['Time'] > 0)]
        d_values.append(df['Time'])
    box_data.extend(d_values)

# Prepare figure and axis
fig, ax = plt.subplots(figsize=(14, 7))

# Calculate positions with gaps
num_boxes = len(labels)  # number of boxes per group
box_width = 0.6
gap_between_boxes = 0.2
group_gap = 1  # gap between groups

# Calculate positions for each box
positions = []
for group in range(2):
    group_start = group * (num_boxes * (box_width + gap_between_boxes) + group_gap)
    for box in range(num_boxes):
        positions.append(group_start + box * (box_width + gap_between_boxes))

# Create box plots
box = ax.boxplot(box_data, positions=positions, widths=box_width, patch_artist=True, showfliers=False)

for i, d in enumerate(box_data):
    # Draw each box plot, coloring the first box black
    if len(d) == 0:
        ax.plot([positions[i]], [60], 'r_', markersize=15)

# Style parameters
colors = ['black'] + ['white'] * (len(labels) - 1)
patterns = [''] + ['\\' * 3] * 5 + [''] * 5

# Style each box in box plot
for i, (patch, color, pattern) in enumerate(zip(box['boxes'], colors * 2, patterns * 2)):
    patch.set(facecolor=color, hatch=pattern, edgecolor='black')

# Add vertical dotted line between groups
middle_position = (positions[10] + positions[11]) / 2
ax.axvline(x=middle_position, color='black', linestyle=':', linewidth=3, alpha=0.6)

ax.set_xticks(positions)
ax.set_xticklabels([*labels, *labels])
plt.xticks(rotation=38, ha='right', rotation_mode='anchor')
ax.tick_params(axis='x', labelsize=FONT_SIZE + 5, pad=-2, length=5)

# Add x-axis labels for each box
# for i, label in enumerate(labels):
#     # Position for first group
#     ax.text(positions[i],
#             ax.get_ylim()[0] - (ax.get_ylim()[1] - ax.get_ylim()[0]) * 0.05,
#             label,
#             ha='right',
#             va='top',
#             rotation=45,
#             rotation_mode='anchor')
#     # Position for second group
#     ax.text(positions[i + 10],
#             ax.get_ylim()[0] - (ax.get_ylim()[1] - ax.get_ylim()[0]) * 0.05,
#             label,
#             ha='right',
#             va='top',
#             rotation=45,
#             rotation_mode='anchor')

group_positions = [np.mean(positions[:9]), np.mean(positions[9:])]
for i, pos in enumerate(group_positions):
    ax.text(pos + 1,
            68,
            group_labels[i],
            ha='right',  # Changed from 'center' to 'right'
            va='top',
            fontsize=FONT_SIZE + 6
            )

# Add group labels
# group_positions = [np.mean(positions[:9]), np.mean(positions[9:])]
# ax.set_xticks(group_positions)
# ax.set_xticklabels(['D-50', 'D-100'])


# Add legend
# legend_patches = [Patch(facecolor='white', edgecolor='black', hatch=pattern, label=label)
#                   for pattern, label in zip(patterns, labels)]
# ax.legend(handles=legend_patches, loc='upper left')

# Style adjustments
# plt.yscale('log')
ax.set_ylabel('Time (seconds)', fontsize=FONT_SIZE + 6)
ticks = [0, 10, 20, 30, 40, 50, 60]
ax.set_yticks(ticks)
ax.set_yticklabels(ticks, fontsize=FONT_SIZE + 6)
ax.spines['right'].set_visible(False)
ax.spines['top'].set_visible(False)

# Adjust layout to prevent label cutoff
# plt.subplots_adjust(bottom=0.25)

plt.tight_layout()

plt.savefig('plt/RQ3-Fig-12-b.pdf', format='pdf', transparent=True)
