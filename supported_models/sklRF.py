from pandas import read_csv
from numpy import argmax

class SciKitLearnRF:


	def __init__( self, clf=None, dataSet=None ):
		self.dataSet = dataSet
		self.model = clf
		self.make_model_dictionary()#self.modelDictionary
		self.model2csp_functions()#self.modelAsFunctions
		self.model2csp_atomic()#self.modelAsAtoms


	def get_number_of_models( self ):
		return self.model.n_estimators


	def make_model_dictionary( self ):
		ensemble = []
		for modelID in range( self.get_number_of_models() ):
			rootNode = make_node( self.model.estimators_[modelID].tree_, 0 )
			ensemble.append( rootNode )
		self.modelDictionary = ensemble


	def model2csp_functions( self ):
		modelFunctions = []
		for modelID in range(self.get_number_of_models()):
			functionString = '(define-fun m%d (' % ( modelID )
			for attID in range(self.dataSet.get_number_of_attributes()):
				functionString += ' (att%d Real)' % attID
			functionString += ') Real '
			modelFunctions.append( node2csp_function( self.modelDictionary[modelID], modelID, functionString )+')' )
		self.modelAsFunctions = modelFunctions

	def model2csp_atomic( self ):
		modelAtoms = []
		for modelID in range(self.get_number_of_models()):
			constraintDictionary = make_empty_constraint_dictionary()
			modelAtoms.append( node2csp_atomic( self.modelDictionary[modelID], modelID, self.dataSet.get_attribute_names(), constraintDictionary ) )
		self.modelAsAtoms = modelAtoms

def make_empty_constraint_dictionary():
	constraintDictionary = {
		'ruleDeclarations':[],
		'thresholdDeclarations':[],
		'branchDeclarations':[],
		'thresholdAssertions':[],
		'ruleAssertions':[],
		'branchAssertions':[],
		'leafAssertions':[]
	}
	return constraintDictionary


def node2csp_atomic( node, modelID, attributeNames, constraintDictionary ):
	ruleDeclarations = []
	thresholdDeclarations = []
	branchDeclarations = []
	ruleAssertions = []
	thresholdAssertions = []
	branchAssertions = []
	leafAssertions = []

	if not node['is_leaf']:
		ruleDeclarations.append('(declare-const r%d_m%d Bool)' % ( node['node_id'], modelID ))
		thresholdDeclarations.append('(declare-const t%d_m%d Real)' % (node['node_id'], modelID ))
		thresholdAssertions.append('(assert (! (= t%d_m%d %.2f) :named T%d-M%d)); %s threshold' % (
			node['node_id'],
			modelID,
			node['threshold'],
			node['node_id'],
			modelID,
			attributeNames[node['attribute_number']]
		))
		ruleAssertions = ['(assert (! (= r%d_m%d (<= %s t%d_m%d)) :named R%d-M%d)); rule' % (
			node['node_id'],
			modelID,
			attributeNames[node['attribute_number']],
			node['node_id'],
			modelID,
			node['node_id'],
			modelID
		)]
	else:
		#leafAssertions = ['(assert (! (=> b%d_m%d (and (= ensemblePredictionArray (store ensemblePredictionArray %d %d)) (= p_m%d %s))) :named L%d-M%d)); leaf' % (
			#node['node_id'],
			#modelID,
			#modelID,
			#argmax(node['class_counts']),
			#modelID,
			#argmax(node['class_counts']),
			#node['node_id'],
			#modelID
		#)]
		leafAssertions = ['(assert (! (=> b%d_m%d (= p_m%d %s)) :named L%d-M%d)); leaf' % (
			node['node_id'],
			modelID,
			modelID,
			argmax(node['class_counts']),
			node['node_id'],
			modelID
		)]


	if 'left_child' in node.keys():
		branchDeclarations.append('(declare-const b%d_m%d Bool)' % (node['left_child']['node_id'],modelID))
		#branchAssertions.append('(assert (! (= b%d_m%d (and b%d_m%d r%d_m%d)) :named B%d-M%d)); branch' % (
		branchAssertions.append('(assert (= b%d_m%d (and b%d_m%d r%d_m%d))); branch' % (
			node['left_child']['node_id'],
			modelID,
			node['node_id'],
			modelID,
			node['node_id'],
			modelID
		))
			#node['left_child']['node_id'],
			#modelID
		#))
		leftSubTree = node2csp_atomic( node['left_child'], modelID, attributeNames, make_empty_constraint_dictionary() )
	if 'right_child' in node.keys():
		branchDeclarations.append('(declare-const b%d_m%d Bool)' % (node['right_child']['node_id'],modelID))
		#branchAssertions.append('(assert (! (= b%d_m%d (and b%d_m%d (not r%d_m%d))) :named B%d-M%d)); branch' % (
		branchAssertions.append('(assert (= b%d_m%d (and b%d_m%d (not r%d_m%d)))); branch' % (
			node['right_child']['node_id'],
			modelID,
			node['node_id'],
			modelID,
			node['node_id'],
			modelID
		))
			#node['right_child']['node_id'],
			#modelID
		#))
		rightSubTree = node2csp_atomic( node['right_child'], modelID, attributeNames, make_empty_constraint_dictionary() )

	constraintDictionary = add_to_constraint_dictionary(
		constraintDictionary,
		thresholdDeclarations,
		ruleDeclarations,
		branchDeclarations,
		thresholdAssertions,
		ruleAssertions,
		branchAssertions,
		leafAssertions
	)

	if 'left_child' in node.keys():
		ltD, lrD, lbD, ltA, lrA, lbA, llA = extract_subtree_constraints( leftSubTree )
		constraintDictionary = add_to_constraint_dictionary( constraintDictionary, ltD, lrD, lbD, ltA, lrA, lbA, llA )
	if 'right_child' in node.keys():
		rtD, rrD, rbD, rtA, rrA, rbA, rlA = extract_subtree_constraints( rightSubTree )
		constraintDictionary = add_to_constraint_dictionary( constraintDictionary, rtD, rrD, rbD, rtA, rrA, rbA, rlA )

	return constraintDictionary


def extract_subtree_constraints( cd ):
	return cd['thresholdDeclarations'], cd['ruleDeclarations'], cd['branchDeclarations'], cd['thresholdAssertions'], cd['ruleAssertions'], cd['branchAssertions'], cd['leafAssertions']


def add_to_constraint_dictionary( constraintDictionary, thresholdD, ruleD, branchD, thresholdA, ruleA, branchA, leafA ):
	for declaration in thresholdD:
		constraintDictionary['thresholdDeclarations'].append(declaration)
	for declaration in ruleD:
		constraintDictionary['ruleDeclarations'].append(declaration)
	for declaration in branchD:
		constraintDictionary['branchDeclarations'].append(declaration)
	for assertion in thresholdA:
		constraintDictionary['thresholdAssertions'].append(assertion)
	for assertion in ruleA:
		constraintDictionary['ruleAssertions'].append(assertion)
	for assertion in branchA:
		constraintDictionary['branchAssertions'].append(assertion)
	for assertion in leafA:
		constraintDictionary['leafAssertions'].append(assertion)
	return constraintDictionary


def node2csp_function( node, modelID, functionString ):
	if not node['is_leaf']:
		functionString += '(ite (<= att%d t%d_m%d) %s %s)' % (
			node['attribute_number'],
			node['node_id'],
			modelID,
			node2csp_function( node['left_child'], modelID, ''),
			node2csp_function( node['right_child'], modelID, '')
		)
	else:
		functionString += ' %.1f ' % ( argmax( node['class_counts'] ) )
	return functionString


def make_node( sklTree, nodeIdx ):
	nodeDict={'node_id':nodeIdx,'is_leaf':sklTree.children_left[nodeIdx]==sklTree.children_right[nodeIdx]}
	if sklTree.children_left[nodeIdx]> -1:
		nodeDict['threshold'] = sklTree.threshold[nodeIdx]
		nodeDict['attribute_number'] = sklTree.feature[nodeIdx]
		nodeDict['left_child'] = make_node(sklTree,sklTree.children_left[nodeIdx])
	if sklTree.children_right[nodeIdx]> -1:
		nodeDict['threshold'] = sklTree.threshold[nodeIdx]
		nodeDict['attribute_number'] = sklTree.feature[nodeIdx]
		nodeDict['right_child'] = make_node(sklTree,sklTree.children_right[nodeIdx])
	if nodeDict['is_leaf']:
		nodeDict['class_counts']=sklTree.value[nodeIdx][0]
	return nodeDict

