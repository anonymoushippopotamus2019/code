from itertools import chain
from subprocess import Popen
from re import sub
from re import split

class Z3:

	def __init__( self, dataSet=None, model=None ):
		self.dataSet = dataSet
		self.model = model
		self.atomicModels = self.model.modelAsAtoms
		self.quantifiedModels = self.model.modelAsFunctions


#********** Query Function **********

	def declare_query_attribute_values( self ):
		return ['(declare-const %s %s)'%(self.dataSet.get_attribute_name_from_idx(idx),self.dataSet.get_attribute_types()[idx]) for idx in range(self.dataSet.get_number_of_attributes())]

	def assert_query_attribute_values( self, queryDict ):
		self.queryDict = queryDict
		constraints = []
		for key in queryDict.keys():
			constraints.append('(assert (! (= %s %f) :named %s));'%(key,queryDict[key],key+'EQUALS'+'%.0f'%queryDict[key]))
		return constraints

	def declare_query_target( self ):
		return ['(declare-const queryTarget Real)']

	def assert_query_target( self, value ):
		return ['(assert (= queryTarget %d))'%(value)]

	def assert_query_search_bounds( self ):
		constraints = []
		minsAndMaxs = self.dataSet.get_attribute_bounds()
		for idx in range(self.dataSet.get_number_of_attributes()):
			constraints.append('(assert (and (>= %s %f) (<= %s %f)))' % (
				self.dataSet.get_attribute_name_from_idx(idx),
				minsAndMaxs[idx][0],
				self.dataSet.get_attribute_name_from_idx(idx),
				minsAndMaxs[idx][1]
			))
		return constraints

	def assert_query_binary_search_bounds( self ):
		constraints = []
		for idx in range(self.dataSet.get_number_of_attributes()):
			constraints.append('(assert (or (= %s 0) (= %s 1) ))' % (
				self.dataSet.get_attribute_name_from_idx(idx),
				self.dataSet.get_attribute_name_from_idx(idx)
			))
		return constraints
#********** End Query Functions **********



#********** Atomic Model Functions **********
	
	def soft_assert_atomic_constraints( self, constraintType, weight=1 ):
		softAssertions = []
		for modelID in range(len(self.atomicModels)):
			for constraintID in range(len(self.atomicModels[modelID][constraintType])):
				softAssertions.append(self.atomicModels[modelID][constraintType][constraintID].replace('assert','assert-soft').replace('));',') :weight %d);' % (weight)))
		return softAssertions

	def declare_thresholds( self ):
		return list(chain.from_iterable([model['thresholdDeclarations'] for model in self.atomicModels]))

	def assert_thresholds( self ):
		return list(chain.from_iterable([model['thresholdAssertions'] for model in self.atomicModels]))

	def declare_rules( self ):
		return list(chain.from_iterable([model['ruleDeclarations'] for model in self.atomicModels]))

	def assert_rules( self ):
		return list(chain.from_iterable([model['ruleAssertions'] for model in self.atomicModels]))

	def declare_branches( self ):
		root = ['(declare-const b0_m%d Bool)'%(modelID) for modelID in range(self.model.get_number_of_models())]
		root = root + ['(assert b0_m%d)'%(modelID) for modelID in range(self.model.get_number_of_models())]
		return root + list(chain.from_iterable([model['branchDeclarations'] for model in self.atomicModels]))

	def assert_branches( self ):
		return list(chain.from_iterable([model['branchAssertions'] for model in self.atomicModels]))

	def assert_leaves( self ):
		return list(chain.from_iterable([model['leafAssertions'] for model in self.atomicModels]))

	def declare_predictions( self ):
		return ['(declare-const p_m%d Int)'%(modelID) for modelID in range(self.model.get_number_of_models())]

	def declare_ensemble_prediction_array( self ):
		return ['(declare-const ensemblePredictionArray (Array Int Int))']

	def assert_ensemble_prediction_array( self ):
		assertRA = '(assert (= ensemblePredictionArray '
		assertRA += '(store ' * self.model.get_number_of_models()
		assertRA += 'ensemblePredictionArray'
		for element in [' %d p_m%d)'%(idx,idx) for idx in range(self.model.get_number_of_models())]:
			assertRA += element
		assertRA += '))'
		return [assertRA] #maybe need to assert that selects are equal to p_m* too

	def declare_function_count_key_in_array( self, key):
		return ['(declare-fun C%d_count (Int) Int)'%key, '(assert (= (C%d_count -1) 0))'%key]

	def assert_function_count_key_in_array( self, key ):
		bounds = '(and (>= iC%d_count 0) (< iC%d_count %d))'%(key,key,self.model.get_number_of_models())
		check = '(= %d (select ensemblePredictionArray iC%d_count))'%(key, key)
		fi = '(= (C%d_count iC%d_count) (+ (C%d_count (- iC%d_count 1)) 1))'%(key,key,key,key)
		esle = '(= (C%d_count iC%d_count) (+ (C%d_count (- iC%d_count 1)) 0))'%(key,key,key,key)
		assertion = '(assert (forall ((iC%d_count Int)) (=> %s (ite %s %s %s))))'%(key,bounds,check,fi,esle)
		return [assertion, self.declare_tag('C%d_count'%key), self.assert_tag('C%d_count'%key,self.model.get_number_of_models()-1)]

	def declare_ensemble_prediction_votes( self ):
		return ['(declare-const ensembleVotes (Array Int Int))']

	def assert_ensemble_prediction_votes( self ):
		assertRA = '(assert (= ensembleVotes '
		assertRA += '(store ' * len(self.dataSet.targetMap)
		assertRA += 'ensembleVotes'
		for element in [' %d C%d_count_eval)' % (idx,idx) for idx in range(len(self.dataSet.targetMap))]:
			assertRA += element
		assertRA += '))'
		return [assertRA]

	def declare_function_max_of_array( self ):
		return ['(declare-fun consensus (Int) Int)','(assert (= (consensus 0) 0))']

	def assert_function_max_of_array( self ):
		bounds = '(and (> iconsensus 0) (<= iconsensus %d))' % (len(self.dataSet.targetMap)-1)
		check = '(> (select ensembleVotes iconsensus) (select ensembleVotes (- iconsensus 1)))'
		fi = '(= (consensus iconsensus) iconsensus)'#i'm saving the index
		esle = '(= (consensus iconsensus) (consensus (- iconsensus 1)))'
		return ['(assert (forall ((iconsensus Int)) (=> %s (ite %s %s %s))))'%(bounds, check, fi, esle),self.declare_tag('consensus'),self.assert_tag('consensus',len(self.dataSet.targetMap)-1)]

	def declare_human_expectation_for_query_target( self ):
		return ['(declare-const humanExpectation Real)']

	def assert_human_expectation_for_query_target( self, value ):
		return ['(assert (! (= humanExpectation %d) :named GROUNDTRUTH_%d))'%(value,value),'(assert (! (= consensus_eval humanExpectation) :named MACHINE_AGREEMENT))']

	def declare_tag( self, name ):
		return '(declare-const %s_eval Real)' % (name)

	def assert_tag( self, name, bound ):
		return '(assert (= %s_eval (%s %d)))' % (name, name, bound)

#********** Z3 **********

	def set_options_true( self, options ):
		return ['(set-option :%s true)'%(option) for option in options]

	def set_logic( self, logic ):
		return ['(set-logic %s)'%(logic)]

	def conclude( self ):
		return ['(check-sat)','(get-unsat-core)','(get-model)','(exit)']



#*********** Objectives **********
	def assert_maximal_confusion( self ):
		constraint='(assert (and'
		for idx1 in range(len(self.dataSet.targetMap)):
			for idx2 in range(idx1+1,len(self.dataSet.targetMap)):
				constraint += ' (= C%d_count_eval C%d_count_eval)'%(idx1,idx2)
		return [constraint+'))']

	def get_training_predictions_from_each_model( self ):
		declarations=[]
		assertions=[]
		for modelID in range(self.model.get_number_of_models()):
			declaration = '(declare-const training_data_predictions_from_quantified_m%d (Array Int Int))'%(modelID)
			for rowID in range(self.dataSet.data.shape[0]):
				#assertion = '(assert (= training_data_predictions_from_quantified_m%d '%(modelID)
				assertion = '(assert (= training_data_predictions_from_quantified_m%d (store training_data_predictions_from_quantified_m%d %d (quantified_m%d training_row_%d))))'%(modelID,modelID,rowID,modelID,rowID)
				#assertion += '(store ' * 10#self.dataSet.data.shape[0]
				#assertion += 'training_data_predictions_from_quantified_m%d'%(modelID)
				#for elem in [' %d (quantified_m%d training_row_%d))'% (idx,modelID,idx) for idx in range(10)]:#range(self.dataSet.data.shape[0])]:
					#assertion += elem
				#assertion += '))'
				assertions.append(assertion)
			declarations.append(declaration)
		return declarations+assertions

	def declare_training_votes( self ):
		declarations = []
		for rowID in range(self.dataSet.data.shape[0]):
			declarations.append('(declare-const votes_for_training_row_%d (Array Int Int))'%(rowID))
		return declarations

	def assert_training_votes( self ):
		assertions = []
		for rowID in range(self.dataSet.data.shape[0]):
			for modelID in range(self.model.get_number_of_models()):
				assertions.append('(assert (= votes_for_training_row_%d (store votes_for_training_row_%d %d %s)))'%(rowID,rowID,modelID,('(select training_data_predictions_from_quantified_m%d %d)'%(modelID,rowID))))
		return assertions

	def declare_consensus_functions_for_training_data( self ):
		declarations=[]
		assertions=[]
		for classID in range(len(self.dataSet.targetMap)):
			for rowID in range(self.dataSet.data.shape[0]):
				declarations.append('(declare-fun C%d_train%d_count (Int) Int)'%(classID,rowID))
				declarations.append('(assert (= (C%d_train%d_count -1) 0))'%(classID,rowID))

				bounds = '(and (>= iC%d_train%d_count 0) (< iC%d_train%d_count %d))'%(classID,rowID,classID,rowID,self.model.get_number_of_models())
				check = '(= %d (select votes_for_training_row_%d iC%d_train%d_count))'%(classID,rowID,classID,rowID)
				fi = '(= (C%d_train%d_count iC%d_train%d_count) (+ (C%d_train%d_count (- iC%d_train%d_count 1)) 1))'%(classID,rowID,classID,rowID,classID,rowID,classID,rowID)
				esle = '(= (C%d_train%d_count iC%d_train%d_count) (+ (C%d_train%d_count (- iC%d_train%d_count 1)) 0))'%(classID,rowID,classID,rowID,classID,rowID,classID,rowID)
				assertion = '(assert (forall ((iC%d_train%d_count Int)) (=> %s (ite %s %s %s))))'%(classID,rowID,bounds,check,fi,esle)
				assertions.append(assertion)
				assertions.append(self.declare_tag('C%d_train%d_count'%(classID,rowID)))
				assertions.append(self.assert_tag('C%d_train%d_count'%(classID,rowID),self.model.get_number_of_models()-1))
		return declarations+assertions

	def evaluate_consensus_functions_for_training_data( self ):
		declarations = []
		assertions = []
		for rowID in range(self.dataSet.data.shape[0]):
			declarations.append('(declare-const train%d_ensembleVotes (Array Int Int))'%(rowID))
			for classID in range(len(self.dataSet.targetMap)):
				assertions.append('(assert (= train%d_ensembleVotes (store train%d_ensembleVotes %d C%d_train%d_count_eval)))'%(rowID,rowID,classID,classID,rowID))
		return declarations+assertions

	def reach_consensus_for_training_data( self ):
		declarations = []
		assertions = []
		for rowID in range(self.dataSet.data.shape[0]):
			declarations.append('(declare-fun train%d_consensus (Int) Int)'%(rowID))
			declarations.append('(assert (= (train%d_consensus 0) 0))'%(rowID))
			bounds = '(and (> train%d_iconsensus 0) (<= train%d_iconsensus %d))' % (rowID,rowID,len(self.dataSet.targetMap)-1)
			check = '(> (select train%d_ensembleVotes train%d_iconsensus) (select train%d_ensembleVotes (- train%d_iconsensus 1)))'%(rowID,rowID,rowID,rowID)
			fi = '(= (train%d_consensus train%d_iconsensus) train%d_iconsensus)'%(rowID,rowID,rowID)
			esle = '(= (train%d_consensus train%d_iconsensus) (train%d_consensus (- train%d_iconsensus 1)))'%(rowID,rowID,rowID,rowID)
			assertion = '(assert (forall ((train%d_iconsensus Int)) (=> %s (ite %s %s %s))))'%(rowID,bounds,check,fi,esle)
			assertions.append(assertion)
			assertions.append(self.declare_tag('train%d_consensus'%(rowID)))
			assertions.append(self.assert_tag('train%d_consensus'%(rowID),len(self.dataSet.targetMap)-1))
		return declarations+assertions

	def collect_train_data_predictions( self ):
		declarations = ['(declare-const ensemble_predictions_on_train_data (Array Int Int))']
		assertions = []
		for rowID in range(self.dataSet.data.shape[0]):
			assertions.append('(assert (= ensemble_predictions_on_train_data (store ensemble_predictions_on_train_data %d train%d_consensus_eval)))'%(rowID,rowID))
		return declarations + assertions

	def count_correct_training_data_predictions( self ):
		assertions=[]
		declarations=['(declare-fun correct_counter (Int) Int)']
		declarations.append('(assert (= (correct_counter -1) 0))')

		bounds = '(and (>= icorrect_counter 0) (< icorrect_counter %d))'%(self.dataSet.data.shape[0])
		check = '(= (select ensemble_predictions_on_train_data icorrect_counter) (select training_targets icorrect_counter))'
		fi = '(= (correct_counter icorrect_counter) (+ (correct_counter (- icorrect_counter 1)) 1))'
		esle = '(= (correct_counter icorrect_counter) (+ (correct_counter (- icorrect_counter 1)) 0))'
		assertions.append('(assert (forall ((icorrect_counter Int)) (=> %s (ite %s %s %s))))'%(bounds,check,fi,esle))
		assertions.append(self.declare_tag('correct_counter'))
		assertions.append(self.assert_tag('correct_counter',self.dataSet.data.shape[0]))
		return declarations + assertions


	def assert_no_loss_of_train_accuracy( self, acc ):
		assertion = ['(assert (! (>= (/ correct_counter_eval %f) %f) :named train_accuracy_lowered));'%(self.dataSet.data.shape[0],acc)]
		return assertion
	#def assert_function_max_of_array( self ):
		#bounds = '(and (> iconsensus 0) (<= iconsensus %d))' % (len(self.dataSet.targetMap)-1)
		#check = '(> (select ensembleVotes iconsensus) (select ensembleVotes (- iconsensus 1)))'
		#fi = '(= (consensus iconsensus) iconsensus)'#i'm saving the index
		#esle = '(= (consensus iconsensus) (consensus (- iconsensus 1)))'
		#return ['(assert (forall ((iconsensus Int)) (=> %s (ite %s %s %s))))'%(bounds, check, fi, esle),self.declare_tag('consensus'),self.assert_tag('consensus',len(self.dataSet.targetMap)-1)]
#
	#def declare_human_expectation_for_query_target( self ):
		#return ['(declare-const humanExpectation Real)']

	#def assert_function_count_key_in_array( self, key ):
		#bounds = '(and (>= iC%d_count 0) (< iC%d_count %d))'%(key,key,self.model.get_number_of_models())
		#check = '(= %d (select ensemblePredictionArray iC%d_count))'%(key, key)
		#fi = '(= (C%d_count iC%d_count) (+ (C%d_count (- iC%d_count 1)) 1))'%(key,key,key,key)
		#esle = '(= (C%d_count iC%d_count) (+ (C%d_count (- iC%d_count 1)) 0))'%(key,key,key,key)
		#assertion = '(assert (forall ((iC%d_count Int)) (=> %s (ite %s %s %s))))'%(key,bounds,check,fi,esle)
		#return [assertion, self.declare_tag('C%d_count'%key), self.assert_tag('C%d_count'%key,self.model.get_number_of_models()-1)]

#********** Run Scripts **********

def script2file( fileName, script ):
	filePointer = open(fileName+'.smt2', 'w')
	for constraint in script:
		filePointer.write(constraint+'\n')
	filePointer.close()

def run_z3_script( z3_script, postfix ):
	p = Popen(['z3',z3_script+'.smt2'],stdout=open(z3_script+postfix,'w'))
	p.communicate()

def load_sat_model( fileName ):
	filePointer = open( fileName, 'r' )
	fileContent = filePointer.read()
	filePointer.close()

	fileContent = sub('\n','',fileContent)
	fileContent = split('model',fileContent)[1]
	fileContent = split('  \(define-fun ',fileContent)
	fileContent = [fileContent[idx].strip('( ').split() for idx in range(len(fileContent)) if '!' not in fileContent[idx]]
	model = {}
	for lineIdx in range(1,len(fileContent)):
		if fileContent[lineIdx][2] == 'Bool':
			model[fileContent[lineIdx][0]] = True if fileContent[lineIdx][3]=='true)' else False
		elif fileContent[lineIdx][2] == 'Real':
			if fileContent[lineIdx][3] == '(/':
				model[fileContent[lineIdx][0]] = float(fileContent[lineIdx][4])/float(fileContent[lineIdx][5].strip(')'))
			elif fileContent[lineIdx][3] == '(-':
				if fileContent[lineIdx][4] == '(/':
					model[fileContent[lineIdx][0]] = -float(fileContent[lineIdx][5])/float(fileContent[lineIdx][6].strip(')'))
				else:
					model[fileContent[lineIdx][0]] = -float(fileContent[lineIdx][4].strip(')'))
			else:#next element is real number
				model[fileContent[lineIdx][0]] = float(fileContent[lineIdx][3].strip(')'))
		elif fileContent[lineIdx][2] == '(Array':
			model[fileContent[lineIdx][0]] = '('+' '.join(fileContent[lineIdx][2:])

	return model


def load_unsat_core( fileName ):
	filePointer = open( fileName, 'r' )
	fileContent = filePointer.read()
	filePointer.close()
	fileContent = sub('\n','',fileContent)
	fileContent = split('unsat',fileContent)[-1]
	fileContent = split('\(error',fileContent)[0]
	return fileContent.strip('()').split()

def get_query_from_SAT_model( satModel, ds ):
	query = {}
	for attribute in ds.get_attribute_names():
		try:
			query[attribute]=satModel[attribute]
		except:
			print('Cannot find %s in SAT model' % attribute )
	return query

def remove_query_from_solution_set( query, idx ):
	constraint = '(assert (! (not (and'
	for key in query.keys():
		constraint += ' (= %s %s)'%(key,query[key])
	constraint += ')) :named SATQ-%d));'%(idx)
	return constraint
