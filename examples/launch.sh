#!/bin/bash
shopt -s nullglob
DIR="$(dirname "${BASH_SOURCE[0]}")/"
FILES=($DIR*.p)
zenonc="$DIR../znmh -x arith"
card=${#FILES[*]}
fails=0
success=0
timeout="30s"

echo "$card files to check."
echo -ne "success: $success/$card, fails: $fails/$card\r"
 
for ((j=0; j < card; j++))
do
	i=${FILES[$j]}
	if $zenonc -max-time $timeout $i > /dev/null 2>&1; then
		$zenonc -max-time $timeout $i -odk > $i\.dk 2> /dev/null
		if dkcheck -nl $i\.dk > /dev/null 2>&1; then 
			echo -e "\e[32mSUCCESS\e[0m File '$i' was successfully checked."
		else echo -e "\e[31mCHECK FAIL\e[0m File '$i'."
		fi
		rm $i\.dk
		((success++))
	else
		((fails++))
		if [[ "$1" == "-d" ]]; then
			echo -e "\e[1K$i"
		fi
	fi
	echo -ne "success: $success/$card, fails: $fails/$card\r"
done
echo ""
echo "FINISHED"
if (($fails > 0)) 
then exit -1
fi

