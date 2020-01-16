set terminal pdf
set output "RG_OnlyImprovedFitness.pdf"
set style line 1 \
    linecolor rgb '#0060ad' \
    linetype 1 linewidth 2 \
    pointtype 7 pointsize 0.5

plot 'RandomGenFitnessStrictlyImproved.dat' with linespoints linestyle 1
