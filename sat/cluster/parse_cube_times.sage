from sys import *

stat = []
for line in open(argv[1]):
	L = line.split()
	if len(L) > 4 and L[0] == 'c' and L[1] == 'CUBE':
		number = int(L[2])
		assert(L[3] == 'UNSATISFIABLE') 
		assert(L[4] == 'in') 
		time = float(L[5])
		stat.append(time)

stat.sort()
print(stat)

print("total cubes:",len(stat))
print("total time:",sum(stat))
print("average time per cube:",sum(stat)/len(stat))
print("maximum time:",max(stat))

plt_fp = argv[1]+'.logplot.png'
#plt = [point2d((i+1,t),marker='o') for i,t in enumerate(stat)]
#sum(plt).save(plt_fp)
list_plot(stat, scale='semilogy').save(plt_fp)
print(f"wrote plot to {plt_fp}")
