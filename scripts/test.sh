#!/bin/sh

LOGNAME="logs/$1.log"

if [ ! -f $LOGNAME ]; then
  python main.py --p $2 --synthesise --tlsf $3 > $LOGNAME 2>&1
# Log command line too
  echo "python main.py --p $2 --synthesise --tlsf $3 > $LOGNAME 2>&1" >> $LOGNAME
else
  echo "Found $LOGNAME, so I won't run symtri"  
fi

# result
grep ealizable. $LOGNAME | head -n1

TOTAL=$(grep "Synthesis took" $LOGNAME | sed 's/.*took: *//g' | awk '{total = $1/1000} END {printf "%.2f", total}')
ABS=$(grep PredicateAbstr $LOGNAME | sed 's/.*took//g' | awk '{sum+=$1} END {printf "%.2f", sum }')
SAFETY=$(grep safety $LOGNAME | sed 's/.*took//g' | awk '{sum+=$1} END {printf "%.2f", sum }')
LIVENESS=$(grep liveness $LOGNAME | sed 's/.*took//g' | awk '{sum+=$1} END {printf "%.2f", sum }')
COMP=$(grep mismatch $LOGNAME | sed 's/.*took//g' | awk '{sum+=$1} END {printf "%.2f", sum }')
SYNTH=$(grep ltl $LOGNAME | sed 's/.*took//g' | awk '{sum+=$1} END {printf "%.2f", sum }')
SAFETYSTEPS=$(grep safety $LOGNAME | wc -l )
LIVENESSSTEPS=$(grep liveness $LOGNAME | wc -l)

grep states $LOGNAME | grep transitions | head -n1
grep INFO $LOGNAME | grep "abstracting with" | tail -n1

echo "% REFINEMENTS"
echo "& $SAFETYSTEPS % safety"
echo "& $LIVENESSSTEPS % liveness"
echo
echo "% TIME"
echo "& $TOTAL % total"
echo "& $ABS % abstraction"
echo "& $SAFETY % safety"
echo "& $LIVENESS % liveness"
echo "& $COMP % compatibility"
echo "& $SYNTH % synthesis"

