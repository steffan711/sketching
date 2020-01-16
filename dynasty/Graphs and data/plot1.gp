set terminal pdf
set output "UpdatedFitness.pdf"
set style line 1 \
    linecolor rgb '#0060ad' \
    linetype 1 linewidth 2 \
    pointtype 7 pointsize 0.5

plot 'MutationOnlyFitness.dat' with linespoints linestyle 1
