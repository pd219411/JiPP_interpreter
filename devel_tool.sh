VERBOSE=$1

function Check {
	expected=$1
	retval=$?
	[ $retval -eq $expected ] && echo "OK"
	[ $retval -ne $expected ] && echo "ERROR"
}

function CheckDirectory {
	directory=$1
	expected=$2
	for file in "$directory"/* ; do
		cat "$file" | runhaskell ./type_checker.hs
		Check $expected
		[ $VERBOSE ] && cat "$file"
	#echo "$f" "${f%.xls}.csv";
	done
}

CheckDirectory "bad" 1
CheckDirectory "good" 0
