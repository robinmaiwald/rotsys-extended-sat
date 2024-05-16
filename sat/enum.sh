for n in {4..7}; do 
	echo "n = $n:"
	python rotsys.py -a -l $n      | grep count | grep -oE '[^ ]+$'; 
	python rotsys.py -a -l $n -c   | grep count | grep -oE '[^ ]+$'; 
	python rotsys.py -a -l $n -hc  | grep count | grep -oE '[^ ]+$'; 
	python rotsys.py -a -l $n -cm  | grep count | grep -oE '[^ ]+$'; 
	python rotsys.py -a -l $n -scm | grep count | grep -oE '[^ ]+$'; 
	python rotsys.py -a -l $n -gt  | grep count | grep -oE '[^ ]+$'; 
done