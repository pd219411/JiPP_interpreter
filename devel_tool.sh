VERBOSE=$1

function Check {
	expected=$1
	retval=$2
	[ $retval -eq $expected ] && echo 0
	[ $retval -ne $expected ] && echo 1
}

function CheckDirectory {
	directory=$1
	expected=$2
	for file in "$directory"/* ; do
		output=$(cat "$file" | ./type_checker)
		#cat "$file" | runhaskell ./type_checker.hs
		is_ok=$(Check $expected $?)
		#echo "$is_ok"
		if [ $is_ok -eq 0 ]; then
			echo "OK $file"
			[ $VERBOSE -eq 1 ] && cat "$file"
			[ $VERBOSE -eq 1 ] && echo "$output"
		fi

		if [ $is_ok -ne 0 ]; then
			echo "ERROR $file"
			[ $VERBOSE -eq 1 ] && cat "$file"
			[ $VERBOSE -eq 1 ] && echo "$output"
		fi
	#echo "$f" "${f%.xls}.csv";
	done
}

CheckDirectory "bad" 1
CheckDirectory "good" 0
