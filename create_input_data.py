#! /usr/local/bin/sage -python

import os
import sys
# This needs to be run outside the shell, before the script
# os.system("ulimit -n 4096")
from lmfdb import db
label = sys.argv[1]
cols =  ['pointless', 'q_gonality_bounds', 'qbar_gonality_bounds', 'genus']
data = db.gps_gl2zhat_fine.lookup(label, cols)
pointless = data['pointless']
q_bounds = data['q_gonality_bounds']
qbar_bounds = data['q_gonality_bounds']
g = data['genus']

models = [x for x in db.modcurve_models.search({'modcurve' : label})]
var_strip = "XYZWTUVRSABCDEFGHIKLMNOPQJ".lower()
output_lines = []
model_types = []

for idx,model in enumerate(models):
    nvars = model['number_variables']
    model_types.append(model['model_type'])
    if (model['model_type'] in [0,2,8]) or (g == 1):
        # canonical model / plane model / embedded model in projective space
        if nvars <= 26:
            var = ",".join([c for c in var_strip[:nvars]])
        else:
            var = "[x]"
        eqs = ",".join(model['equation'])
        proj_str = "P%s<%s> := ProjectiveSpace(Rationals(), %s);" % (idx, var, nvars-1)
        model_str = "X%s := Curve(P%s, [%s]);" % (idx, idx, eqs)
        output_lines += [proj_str, model_str]
    elif model['model_type'] == 5:
        # elliptic or hyperelliptic over Q
        f = model['equation'][0]
        proj_str = "P%s<x, y, z> := WeightedProjectiveSpace(Rationals(), [1,%s,1]);" % (idx, g+1)
        curve_str = "C%s := Curve(Scheme(P%s, %s));" %(idx, idx, f)
        model_str = "_, X%s := IsHyperelliptic(C%s);" %(idx, idx)
        output_lines += [proj_str, curve_str, model_str]
    else:
        raise NotImplementedError("Not implemented for this model type")
    

model_names = ",".join([("X%s" % i) for i in range(len(models))])
model_types_str = ",".join([("%s" % t) for t in model_types])
output_lines.append("models := [%s];" % model_names)
output_lines.append("model_types := [%s];" % model_types_str)
os.system("mkdir -p input_data")
pointless_str = "pointless := " + str(pointless).lower() + ";"
q_bounds_str = "q_bounds := " + str(q_bounds) + ";"
qbar_bounds_str = "qbar_bounds := " + str(qbar_bounds) + ";"
output_lines += [pointless_str, q_bounds_str, qbar_bounds_str];
return_str = "return pointless, q_bounds, qbar_bounds, models, model_types;"
output_lines.append(return_str)
output = "\n".join(output_lines)
f = open("input_data/" + label, 'w')
f.write(output)
f.close()
