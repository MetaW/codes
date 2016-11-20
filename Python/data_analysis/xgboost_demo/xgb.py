import numpy as np
import pandas as pd
import xgboost as xgb
import sklearn as skl

#========== load train data and split them
train_data = pd.read_csv("train.csv")

#split target attribute and input attribute
train_res = pd.concat([train_data.Id, train_data.Score], axis=1)
train_data = train_data.drop("Score", axis=1)

tsp = train_data.shape

#load test data
test_data = pd.read_csv("test.csv")


#concate train_data and test_data together(for one hot encoding)
#ID :: train:[1,40000], test:[40001,50999]
test_data.index += tsp[0]
all_data = pd.concat([train_data, test_data], axis=0)



# transfer to one hot encoding
all_data = pd.get_dummies(all_data)


# split test_data and train_data
final_train = all_data.iloc[:tsp[0]]
final_test = all_data.iloc[tsp[0]:]


#split train set into new train set & validation set & test set
train_X = final_train[:int(final_train.shape[0]*0.7)]
valid_X = final_train[int(final_train.shape[0]*0.7):int(final_train.shape[0]*0.85)]
test_X 	= final_train[int(final_train.shape[0]*0.85):]

train_Y = train_res[:int(train_res.shape[0]*0.7)]
valid_Y = train_res[int(train_res.shape[0]*0.7):int(final_train.shape[0]*0.85)]
test_Y	= train_res[int(train_res.shape[0]*0.85):]

# Id is a useless attribute, we can drop this attribute
train_X = train_X.drop("Id", axis=1)
train_Y = train_Y.drop("Id", axis=1)
valid_X = valid_X.drop("Id", axis=1)
valid_Y = valid_Y.drop("Id", axis=1)
test_X 	= test_X.drop("Id", axis=1)
test_Y	= test_Y.drop("Id", axis=1)


##### square target
#train_Y = train_Y.applymap(lambda x: np.math.log(x))
#####


#way 1: with grid search
#====================================================
param_grid = {
	"max_depth": [4,5,6,7], 
	"min_child_weight": [1,3,5],
	"learning_rate": [0.01,0.1,0.3],
	"objective": ['count:poisson', 'reg:linear'],
}


grid_search = skl.model_selection.GridSearchCV(	xgb.XGBRegressor(n_estimators=60, silent=False), 
											   	param_grid,		#param grid for XGBRegressor 
												scoring = 'neg_mean_squared_error', 
												cv = 5, 
												n_jobs = 1)

grid_search.fit(train_X, train_Y)

print("rmse is %f" % np.math.sqrt(-grid_search.best_score_))

'''
grid_search.best_score_:
-14.440976505117657

grid_search.best_params_:
{'learning_rate': 0.1,
 'max_depth': 5,
 'min_child_weight': 1,
 'objective': 'reg:linear'}

grid_search.best_estimator_:
XGBRegressor(base_score=0.5, colsample_bylevel=1, colsample_bytree=1, gamma=0,
       learning_rate=0.1, max_delta_step=0, max_depth=5,
       min_child_weight=1, missing=None, n_estimators=60, nthread=-1,
       objective='reg:linear', reg_alpha=0, reg_lambda=1,
       scale_pos_weight=1, seed=0, silent=False, subsample=1)

'''



# way 2: without grid search
#====================================================
xgb_train_X = xgb.DMatrix(train_X, label=train_Y)
#xgb_valid_X = xgb.DMatrix(valid_X, label=valid_Y)
xgb_valid_X = xgb.DMatrix(valid_X)

param = {
	'max_depth'		: 5,
	'eta'			: 0.05,
	#'gamma'			: 20.0,
	'min_child_weight'	: 1,
	#'save_period'	: 0,
	'booster'		: 'gbtree',
	'objective'		: 'reg:linear'
	#'objective'		: 'count:poisson'
}

num_round = 60

bst = xgb.train(param, xgb_train_X, num_round)

#type: DataFrame
pred = bst.predict(xgb_valid_X)
pred = pd.DataFrame(pred)

#### recover target
#pred.applymap(lambda x:np.math.e**x)
####

#change type : float -> int64
pred += 0.5
pred = pred.astype("int64")

# make index start from 0
valid_Y.index = range(6000)	#type: DataFrame

rmse = np.math.sqrt(skl.metrics.mean_squared_error(valid_Y,pred))

print("rmse is %f" % rmse)

