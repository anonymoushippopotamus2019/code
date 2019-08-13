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


	def set_categorical_string_attributes_to_reals( self ):
		for idx in range( self.get_number_of_attributes() ):
			self.data[ self.data.columns[idx] ] = self.data[ self.data.columns[idx] ].map({'\'y\'':1,'\'n\'':0,'?':2})


def download_openml_dataset( name ):
	if name is 'vote':
		dataFrame = read_csv( 'https://www.openml.org/data/get_csv/56/dataset_56_vote.arff' )
		target , targetMap = factorize( dataFrame.pop( 'Class' ) )
		return Dataset( dataFrame , target , targetMap, True )
