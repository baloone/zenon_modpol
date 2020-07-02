#!/bin/sh
FILES=(*.p)
#zenonc="../znmh"
zenonc="../zenon_modulo -modulo -modulo-heuri -itptp"
card=${#FILES[*]}
fails=0
success=0
timeout="30s"


echo "$card files to check."
 
for ((j=0; j < card; j++))
do
	i=${FILES[$j]}
	if $zenonc -max-time $timeout $i > /dev/null 2>&1; then
		((success++))
	else
		((fails++))
		if [[ "$1" == "-d" ]]; then
			echo $i 
		fi
	fi
	echo -ne "success: $success/$card, fails: $fails/$card\r"
done
echo ""
echo "FINISHED"


