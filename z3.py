from itertools import chain
from subprocess import Popen
from re import sub
from re import split

class Z3:

	def __init__( self, dataSet=None, model=None ):
		self.dataSet = dataSet
		self.model = model
		self.atomicModels = self.model.modelAsAtoms

#********** Query Function **********

	def declare_query_attribute_values( self ):
		return ['(declare-const %s %s)'%(self.dataSet.get_attribute_name_from_idx(idx),self.dataSet.get_attribute_types()[idx]) for idx in range(self.dataSet.get_number_of_attributes())]

	def assert_query_attribute_values( self, queryDict ):
		self.queryDict = queryDict
		constraints = []
		for key in queryDict.keys():
			constraints.append('(assert (! (= %s %s) :named %s));'%(key,queryDict[key],key+'Equals'+str(queryDict[key])))
		return constraints

	def declare_query_target( self ):
		return ['(declare-const queryTarget Real)']

	def assert_query_target( self, value ):
		return ['(assert (= queryTarget %d))'%(value)]

#********** End Query Functions **********



#********** Atomic Model Functions **********

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
		return ['(assert (! (= humanExpectation %d) :named human))'%(value),'(assert (! (= consensus_eval humanExpectation) :named why-not))']

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
	fileContent = split('unsat',fileContent)[0]
	fileContent = split('define-fun ',fileContent)
	fileContent = [fileContent[idx].strip('( ').split() for idx in range(len(fileContent)) if '!' not in fileContent[idx]]
	model = {}
	for lineIdx in range(1,len(fileContent)):
		if fileContent[lineIdx][2] == 'Bool':
			model[fileContent[lineIdx][0]] = True if fileContent[lineIdx][3]=='true)' else False
		elif fileContent[lineIdx][2] == 'Real':
			if fileContent[lineIdx][3] == '(/':
				model[fileContent[lineIdx][0]] = float(fileContent[lineIdx][4])/float(fileContent[lineIdx][5].strip(')'))
			elif fileContent[lineIdx][3] == '-':
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
