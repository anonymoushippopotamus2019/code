from pandas import read_csv
from pandas import factorize
from re import split

class Dataset:


	UNALLOWED_CHARS ='!@#$%^&*()_+~`=\-\[\]\{\}:;\"\'<>,.\\/?|'
	MAP_TO_SMT_LEGAL_TYPES = {
		'float64' : 'Real',
		'int64' : 'Real',
		'object_' : 'Real'
	}


	def __init__( self , data=None , target=None , targetMap=None, map2Reals=False ):
		self.data = data
		self.target = target
		self.targetMap = targetMap
		self.set_safe_attribute_names()
		if map2Reals:
			self.set_categorical_string_attributes_to_reals()


	def get_attribute_bounds( self ):
		mins = self.data.min(0)
		maxs = self.data.max(0)
		return [[mins[i],maxs[i]] for i in range(self.get_number_of_attributes())]

	def get_attribute_names( self ):
		return self.data.columns


	def get_attribute_name_from_idx( self , idx ):
		return self.data.columns[idx]


	def get_attribute_types( self ):
		return [ Dataset.MAP_TO_SMT_LEGAL_TYPES[ dtype.type.__name__ ] for dtype in self.data.dtypes ]


	def get_number_of_attributes( self ):
		return len( self.data.columns)

	def get_target_type( self ):
		print('for now, assuming all targets will be encoded as Reals')
		return 'Real'

	def set_safe_attribute_names( self ):
		for attributeName in self.data.columns:
			self.data = self.data.rename(columns = {attributeName : ''.join([word.capitalize() for word in split('['+Dataset.UNALLOWED_CHARS+']+', attributeName)])})


	def set_categorical_string_attributes_to_reals( self, mapping=None ):
		if mapping:
			for idx in range( self.get_number_of_attributes() ):
				self.data[ self.data.columns[idx] ] = self.data[ self.data.columns[idx] ].map(mapping)
		else:
			attTypes=self.data.dtypes
			for idx in range( self.get_number_of_attributes() ):
				if attTypes[idx].type.__name__ == 'object_':
					self.data[ self.data.columns[idx] ] = factorize( self.data[self.data.columns[idx]], sort=True )[0]

	def declare_training_data( self ):
		declarations = []
		for rowID in range(self.data.shape[0]):
			declarations.append('(declare-const training_row_%d (Array Int Real))'%(rowID))
		return declarations

	def assert_training_data( self ):
		assertions=[]
		for rowID in range(self.data.shape[0]):
			for attID in range(self.data.shape[1]):
			#assertion = '(assert (= training_row_%d ' % rowID
				assertion = '(assert (= training_row_%d (store training_row_%d %d %f)))'%(rowID,rowID,attID,self.data.iloc[rowID][attID])
			#assertion += '(store ' * self.data.shape[1]
			#assertion += 'training_row_%d' % rowID
			#for elem in [' %d %f)' % (idx,self.data.iloc[rowID][idx]) for idx in range(self.data.shape[1])]:
				#assertion += elem
			#assertion += '))'
				assertions.append(assertion)
		return assertions

	def declare_training_targets( self ):
		declaration = '(declare-const training_targets (Array Int Int))'
		return [declaration]

	def assert_training_targets( self ):
		assertions = []
		for rowID in range(self.data.shape[0]):
			assertion = '(assert (= training_targets (store training_targets %d %d)))'%(rowID,self.target[rowID])
			assertions.append(assertion)
		return assertions



def download_openml_dataset( name ):
	if name is 'vote':
		dataFrame = read_csv( 'https://www.openml.org/data/get_csv/56/dataset_56_vote.arff' )
		target , targetMap = factorize( dataFrame.pop( 'Class' ) )
		return Dataset( dataFrame , target , targetMap, True )

def download_openml_dataset_split( name, trainTestSplit ):
	if name is 'vote':
		dataFrame = read_csv( 'https://www.openml.org/data/get_csv/56/dataset_56_vote.arff' )
		train = dataFrame.sample( frac=trainTestSplit )
		test = dataFrame.drop(train.index)
		trainTarget , targetMap = factorize( train.pop( 'Class' ), sort=True )
		testTarget, targetMap = factorize( test.pop( 'Class' ), sort=True )

		trainData = Dataset( train , trainTarget, targetMap )
		trainData.set_categorical_string_attributes_to_reals({'\'y\'':1,'\'n\'':0,'?':2})
		testData = Dataset( test, testTarget, targetMap )
		testData.set_categorical_string_attributes_to_reals({'\'y\'':1,'\'n\'':0,'?':2})
		return trainData, testData

	if name is 'credit':
		dataFrame = read_csv( 'https://www.openml.org/data/get_csv/31/dataset_31_credit-g.arff' )
		train = dataFrame.sample( frac=trainTestSplit )
		test = dataFrame.drop(train.index)
		trainTarget, targetMap = factorize( train.pop('class'), sort=True )
		testTarget, targetMap = factorize( test.pop('class'), sort=True )
		trainData = Dataset( train, trainTarget, targetMap )
		testData = Dataset( test, testTarget, targetMap )
		trainData.set_categorical_string_attributes_to_reals()
		testData.set_categorical_string_attributes_to_reals()
		return trainData, testData

def load_dataset_from_file( fileName ):
	dataFrame = read_csv( fileName )
	#dataFrame.pop('SegmentInfo.FoldID') #comment out if using AutonRFs
	target, targetMap = factorize( dataFrame.pop( 'LABEL' ), sort=True )
	return Dataset( dataFrame, target, targetMap)

def load_dataset_from_file_split( fileName, trainTestSplit ):
	dataFrame = read_csv( fileName )
	#dataFrame.pop('SegmentInfo.FoldID')
	train = dataFrame.sample( frac=trainTestSplit )
	test = dataFrame.drop(train.index)
	trainTarget , targetMap = factorize( train.pop( 'LABEL' ), sort=True )
	testTarget, targetMap = factorize( test.pop( 'LABEL' ), sort=True )
	return Dataset( train, trainTarget, targetMap ), Dataset( test, testTarget, targetMap )
