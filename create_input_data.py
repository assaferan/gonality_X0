#! /usr/local/bin/sage -python

import os
import sys
# This needs to be run outside the shell, before the script
# os.system("ulimit -n 4096")
from lmfdb import db
label = sys.argv[1]
cols =  ['pointless', 'q_gonality_bounds', 'qbar_gonality_bounds']
data = db.gps_gl2zhat_fine.lookup(label, cols)
pointless = data['pointless']
q_bounds = data['q_gonality_bounds']
qbar_bounds = data['q_gonality_bounds']

models = [x for x in db.modcurve_models.search({'modcurve' : label})]
var_strip = "XYZWTUVRSABCDEFGHIKLMNOPQJ".lower()
output_lines = []

for idx,model in enumerate(models):
    if model['model_type'] == 0:
        # embedded model in projective space
        nvars = model['number_variables']
        if nvars <= 26:
            var = ",".join([c for c in var_strip[:nvars]])
        else:
            var = "[x]"
        eqs = ",".join(model['equation'])
        proj_str = "P%s<%s> := ProjectiveSpace(Rationals(), %s);" % (idx, var, nvars-1)
        model_str = "X%s := Curve(P%s, [%s]);" % (idx, idx, eqs)
        output_lines += [proj_str, model_str]

model_names = ",".join([("X%s" % i) for i in range(len(models))])
output_lines.append("models := [%s];" % model_names)
os.system("mkdir -p input_data")
pointless_str = "pointless := " + str(pointless).lower() + ";"
q_bounds_str = "q_bounds := " + str(q_bounds) + ";"
qbar_bounds_str = "qbar_bounds := " + str(qbar_bounds) + ";"
output_lines += [pointless_str, q_bounds_str, qbar_bounds_str];
return_str = "return pointless, q_bounds, qbar_bounds, models;"
output_lines.append(return_str)
output = "\n".join(output_lines)
f = open("input_data/" + label, 'w')
f.write(output)
f.close()
