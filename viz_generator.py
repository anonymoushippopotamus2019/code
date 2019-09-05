from graphviz import Digraph

def viz_query( query ):
	graph = Digraph(name='cluster_inputs',comment='input values',graph_attr={'splines':'spline'})
	lastID=0
	lastName=''
	for attribute in query.keys():
		graph.node(attribute,label=('%s\ninitial=%.0f'%(attribute,query[attribute])).upper(),shape='cds',height='1',fontcolor='black')
		if lastID>0: #we need to invisibly link the nodes to get nice cluster
			graph.edge(lastName,attribute,color='white')
		lastID+=1
		lastName=attribute

	return graph

def viz_rf( branches, rules, leaves, interventions=None, changes=None ):
	NC='black'
	FC='black'
	graph = Digraph(name='models',comment='models',graph_attr={'spline':'spline','rankdir':'TB','ordering':'out'})
	for line in rules:
		elems = [elem.strip('();') for elem in line.split(' ')]
		if interventions:
			FS = '18' if elems[5] in interventions.keys() else '14'
		FC = 'black'#'red' if elems[5] in interventions.keys() else 'black'
		NC = 'black'#'green' if elems[5] in changes.keys() else 'black'
		if interventions and changes:
			if elems[5] in interventions.keys():
				graph.node(elems[2], label='%s\\n%s\\n%s %s = %s -> %s'%(elems[2].upper(),elems[4].upper(),elems[3].upper(),elems[5].upper(),elems[7].upper(),interventions[elems[5]][-1]), fontcolor=FC, fontname='helvetica',color=NC,fontsize = FS,style='bold,dashed',shape='box')
			elif elems[5] in changes.keys():
				graph.node(elems[2], label='%s\\n%s\\n%s %s = %s'%(elems[2].upper(),elems[4].upper(),elems[3].upper(),elems[5].upper(),elems[7]),color= NC, fontname='helvetica',shape='box')
			else:
				graph.node(elems[2], label='%s\\n%s\\n%s %s = %s'%(elems[2].upper(),elems[4].upper(),elems[3].upper(),elems[5].upper(),elems[7]),color= NC, fontname='helvetica',shape='box')
		else:
			graph.node(elems[2], label='%s\\n%s\\n%s %s = %s'%(elems[2].upper(),elems[4].upper(),elems[3].upper(),elems[5].upper(),elems[7]),color= NC, fontname='helvetica',shape='box')

	for line in leaves:
		elems = [elem.strip('();') for elem in line.split(' ')]
		NC = 'black'#'green' if elems[3] in changes.keys() else 'black'
		FC = 'black'#'red' if elems[6]=='0' else 'blue'
		graph.node('r'+elems[3][1:],label=('%s\\n%s = %s'%(('l'+elems[3][1:]).upper(),elems[5].upper(),elems[6].upper())),color=NC, fontcolor=FC, fontname='helvetica',shape='invhouse')
	for line in branches:
		elems = [elem.strip('();') for elem in line.split(' ')]
		atom = elems[6] if elems[5]=='not' else elems[5]
		graph.edge(atom,'r'+elems[2][1:],label=elems[2].upper(),color='black',fontname='helvetica')
		if changes:
			if elems[2] in changes.keys():
				if changes[elems[2]][1]==True:
					graph.edge('r'+elems[2][1:],atom,color='black',style='bold,dashed')
				else:
					graph.edge(atom,'r'+elems[2][1:],color='black',style='bold,dashed')

	return graph
