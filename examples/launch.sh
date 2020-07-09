#!/bin/bash
shopt -s nullglob
DIR="$(dirname "${BASH_SOURCE[0]}")/"
FILES=($DIR*.p)
#zenonc="../znmh"
zenonc="$DIR../zenon_modulo -modulo -modulo-heuri -itptp"
card=${#FILES[*]}
fails=0
success=0
timeout="300s"

echo "$card files to check."
echo -ne "success: $success/$card, fails: $fails/$card\r"
 
for ((j=0; j < card; j++))
do
	i=${FILES[$j]}
	if $zenonc -max-time $timeout $i > /dev/null 2>&1; then
		((success++))
	else
		((fails++))
		if [[ "$1" == "-d" ]]; then
			echo -e "\033[1K$i"
		fi
	fi
	echo -ne "success: $success/$card, fails: $fails/$card\r"
done
echo ""
echo "FINISHED"
if (($fails > 1)) 
then exit -1
fi

