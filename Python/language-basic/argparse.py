import argparse

parser = argparse.ArgumentParser()
parser.add_argument("--solver", help="solver file", type=str)
parser.add_argument("--modelweight", help="model weight", type=str)
parser.add_argument("--solverstate", help="slover state", type=str)
args = parser.parse_args()

if not args.solver:
    print("Error: please give the solver file in the command line with --solver")
    exit(1)

if args.modelweight:
    modelweight_path = args.modelweight
    if not os.path.exists(modelweight_path):
        print("Error: modelweight file: "+modelweight_path+" does not exist!")
        exit(1)

if args.solverstate:
    solverstate_path = args.solverstate
    if not os.path.exists(solverstate_path):
        print("Error: solverstate file: "+solverstate_path+" does not exist!")
        exit(1)
