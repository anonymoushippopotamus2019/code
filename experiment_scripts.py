from sklearn.model_selection import train_test_split
from scipy.spatial.distance import pdist, squareform
from sklearn.ensemble import RandomForestClassifier
from sklearn.model_selection import GridSearchCV
from sklearn.manifold import TSNE
from multiprocessing import Pool
from pandas import concat
from pandas import DataFrame
from pandas import set_option
from os import listdir
from os.path import isfile
from time import sleep
from time import time
from random import choice
from pickle import dump
from pickle import load
from warnings import simplefilter
import matplotlib.pyplot as plt
from matplotlib import offsetbox
import numpy as np 
from z3 import script2file
from z3 import load_sat_model
from z3 import run_z3_script
from z3 import load_unsat_core
from z3 import get_query_from_SAT_model
from z3 import remove_query_from_solution_set
from z3 import Z3

def get_explanation( obj ):
    rowID=obj[0]
    yhat=obj[1]
    ds=obj[2]
    engine=obj[3]
    query={}
    for attnum in range(len(ds.data.columns)):
        query[ds.data.columns[attnum]]=ds.data.iloc[rowID][attnum]

    scriptText = \
        engine.set_options_true(['produce-models',
                                 'produce-unsat-cores',
                                 'smt.core.minimize']) + \
        engine.set_logic('AUFLIRA') + \
        engine.declare_query_attribute_values() + \
        engine.assert_query_attribute_values(query)+ \
        engine.declare_query_target() + \
        engine.assert_query_target(ds.target[rowID]) + \
        engine.declare_ensemble_prediction_array() + \
        engine.declare_thresholds() + \
        engine.assert_thresholds() + \
        engine.declare_rules() + \
        engine.assert_rules() + \
        engine.declare_branches() + \
        engine.assert_branches() + \
        engine.declare_predictions() + \
        engine.assert_leaves() + \
        engine.assert_ensemble_prediction_array()

    for i in range(len(engine.dataSet.targetMap)):
        scriptText += engine.declare_function_count_key_in_array(i)
        scriptText += engine.assert_function_count_key_in_array(i)

    scriptText += \
        engine.declare_ensemble_prediction_votes() + \
        engine.assert_ensemble_prediction_votes() + \
        engine.declare_function_max_of_array() + \
        engine.assert_function_max_of_array() + \
        engine.declare_human_expectation_for_query_target() + \
        engine.assert_human_expectation_for_query_target(ds.target[rowID]) + \
        engine.conclude()

    filename = 'output/why_not_row%d_prediction'%(rowID)
    script2file(filename,scriptText)
    run_z3_script( filename, '.model' )

    # Minimize Unsat Core
    origUnsatCore=load_unsat_core(filename+'.model')
    if '(define-fun' in origUnsatCore:
        return rowID, {'model':'SAT'}
    unsatMarks = {atom:False for atom in origUnsatCore}

    # Multiprocess unsat hypotheses
    num_processors = 40
    p=Pool(processes = num_processors)
    output = p.map(minimize_unsat_core ,[(rowID,scriptText,key,yhat,ds.target[rowID]) for key in unsatMarks])
    p.close()

    output = [x for x in output if x is not None]

    return rowID, output




def minimize_unsat_core(obj):
        rowID=obj[0]
        scriptText = obj[1]
        key = obj[2]
        yhat=obj[3]
        y=obj[4]
        newScript = []
        for line in scriptText:
            if key in line:
                newScript.append(';'+line)
            else:
                newScript.append(line)

        filename = 'output/why_not_row%d_unsat_%s'%(rowID,key)
        script2file(filename,newScript)
        run_z3_script( filename, '.model' )
        currUnsatCore = load_unsat_core('./'+filename+'.model')
        if '(define-fun' in currUnsatCore:
            return key
        return





def get_interventions( obj ):

    rowID = obj[0]
    ds = obj[1]
    clf = obj[2]
    engine=obj[3]
    train=obj[4]
    query={}
    for attnum in range(len(ds.data.columns)):
        query[ds.data.columns[attnum]]=ds.data.iloc[rowID][attnum]

        scriptText = \
        engine.set_options_true(['produce-models',
                                 'produce-unsat-cores',
                                 'smt.core.minimize']) + \
        engine.set_logic('AUFLIRA') + \
        engine.declare_query_attribute_values() + \
        engine.assert_query_attribute_values(query)+ \
        engine.declare_query_target() + \
        engine.assert_query_target(ds.target[rowID]) + \
        engine.declare_ensemble_prediction_array() + \
        engine.declare_thresholds() + \
        engine.assert_thresholds() + \
        engine.declare_rules() + \
        engine.assert_rules() + \
        engine.declare_branches() + \
        engine.assert_branches() + \
        engine.declare_predictions() + \
        engine.assert_leaves() + \
        engine.assert_ensemble_prediction_array()

    for i in range(len(engine.dataSet.targetMap)):
        scriptText += engine.declare_function_count_key_in_array(i)
        scriptText += engine.assert_function_count_key_in_array(i)

    scriptText += \
        engine.declare_ensemble_prediction_votes() + \
        engine.assert_ensemble_prediction_votes() + \
        engine.declare_function_max_of_array() + \
        engine.assert_function_max_of_array() + \
        engine.conclude()


    basefile = 'output/intervention_row%d_base_model'%(rowID)
    script2file(basefile,scriptText)
    run_z3_script( basefile, '.model' )

    interventionScriptText = \
        engine.set_options_true(['produce-models',
                                 'produce-unsat-cores',
                                 'smt.core.minimize']) + \
        engine.set_logic('AUFLIRA') + \
        engine.declare_query_attribute_values() + \
        engine.assert_query_attribute_values(query)+ \
        engine.declare_query_target() + \
        engine.assert_query_target(ds.target[rowID]) + \
        engine.declare_ensemble_prediction_array() + \
        engine.dataSet.declare_training_data() + \
        engine.dataSet.assert_training_data() + \
        engine.dataSet.declare_training_targets() + \
        engine.dataSet.assert_training_targets() + \
        engine.declare_thresholds() + \
        engine.soft_assert_atomic_constraints('thresholdAssertions') + \
        engine.declare_rules() + \
        engine.assert_rules() + \
        engine.declare_branches() + \
        engine.assert_branches() + \
        engine.declare_predictions() + \
        engine.assert_leaves() + \
        engine.model.modelAsFunctions + \
        engine.get_training_predictions_from_each_model() + \
        engine.declare_training_votes() + \
        engine.assert_training_votes() + \
        engine.declare_consensus_functions_for_training_data() + \
        engine.evaluate_consensus_functions_for_training_data() + \
        engine.reach_consensus_for_training_data() + \
        engine.collect_train_data_predictions() + \
        engine.count_correct_training_data_predictions() + \
        engine.assert_no_loss_of_train_accuracy(clf.score(train.data,train.target)) + \
        engine.assert_ensemble_prediction_array()

    for i in range(len(engine.dataSet.targetMap)):
        interventionScriptText += engine.declare_function_count_key_in_array(i)
        interventionScriptText += engine.assert_function_count_key_in_array(i)

    interventionScriptText += \
        engine.declare_ensemble_prediction_votes() + \
        engine.assert_ensemble_prediction_votes() + \
        engine.declare_function_max_of_array() + \
        engine.assert_function_max_of_array() + \
        engine.declare_human_expectation_for_query_target() + \
        engine.assert_human_expectation_for_query_target(ds.target[rowID]) + \
        engine.conclude()

    softfile = 'output/intervention_row%d_soft_model'%(rowID)
    script2file(softfile,interventionScriptText)
    run_z3_script( softfile, '.model' )

    base_model=load_sat_model(basefile+'.model')
    soft_model= load_sat_model(softfile+'.model')

    interventions = {}
    changes= {}
    for key in base_model.keys():
        if key[0].isupper():
            continue
        if key[0]=='b' or key[0]=='r':
            if base_model[key]!=soft_model[key]:
                changes[key]=[base_model[key],soft_model[key]]
        if base_model[key]!=soft_model[key]:
            interventions[key]=[base_model[key],soft_model[key]]
            changes[key]=[base_model[key],soft_model[key]]

    with open('output/intervention_row%d.pkl'%(rowID),'wb') as f:
        dump([rowID,interventions,changes], f)
    print('%d completed'%(rowID))
    return rowID, interventions,changes






def get_distrust_regions( engine, ds, confusingAssertions=[], confusingData=[] ):

    scriptText = \
        engine.set_options_true(['produce-models',
                                 'produce-unsat-cores',
                                 'smt.core.minimize']) + \
        engine.set_logic('AUFLIRA') + \
        engine.declare_query_attribute_values() + \
        engine.declare_ensemble_prediction_array() + \
        engine.assert_query_binary_search_bounds() + \
        engine.declare_thresholds() + \
        engine.assert_thresholds() + \
        engine.declare_rules() + \
        engine.assert_rules() + \
        engine.declare_branches() + \
        engine.assert_branches() + \
        engine.declare_predictions() + \
        engine.assert_leaves() + \
        engine.assert_ensemble_prediction_array()

    for i in range(len(engine.dataSet.targetMap)):
        scriptText += engine.declare_function_count_key_in_array(i)
        scriptText += engine.assert_function_count_key_in_array(i)

    scriptText += \
        engine.declare_ensemble_prediction_votes() + \
        engine.assert_ensemble_prediction_votes() + \
        engine.declare_function_max_of_array() + \
        engine.assert_function_max_of_array() + \
        engine.assert_maximal_confusion()

    for idx in range(len(confusingAssertions)):
        scriptText += [confusingAssertions[idx]]

    scriptText += \
        engine.conclude()

    filename = 'output/confusing_%d'%(len(confusingData))

    script2file(filename,scriptText)
    run_z3_script( filename, '.model' )

    satModel = load_sat_model(filename+'.model')
    confusingQuery = get_query_from_SAT_model(satModel, ds)
    confusingAssertions.append(remove_query_from_solution_set(confusingQuery,len(confusingData)))
    confusingData.append(confusingQuery)
    if(len(confusingData)<500):
        get_distrust_regions(engine,ds,confusingAssertions,confusingData)
    else:
        return confusingData

    return confusingData



def rationalize_behavior_by_category( reasoning, ds, model_predictions ):
    rowID = reasoning[0]
    atoms = reasoning[1]
    leaf_atoms = [elem.replace('-L','L') for elem in atoms if '-L' in elem]
    threshold_atoms = [elem.replace('-T','T')  for elem in atoms if '-T' in elem]
    machine_atoms = [elem for elem in atoms if 'MACHINE' or 'GROUNDTRUTH' in elem]
    input_atoms = [elem.replace('EQUALS','=') for elem in atoms if 'EQUALS' in elem]

    return {'input':input_atoms, 'threshold':threshold_atoms, 'leaf':leaf_atoms, 'machine':machine_atoms}




def get_cdist(X,y):
    dists = squareform(pdist(X))
    res = {}
    for i in np.unique(y):
        for j in np.unique(y):
            d1 = dists[np.where(y==i)]
            d2 = d1[:,np.where(y == j)]
            d2 = np.squeeze(d2)
            if i == j:
                total = d2.sum()
                meanv = total/((d2.shape[0]-1)*(d2.shape[1]))
            else:
                meanv = d2.mean()
            res[(i,j)] = meanv
    return res
