#!/usr/bin/env python3

import subprocess
import sys, os, glob
import csv
from pathlib import Path
from typing import Tuple, List
from enum import Enum

Benchmark = str
Data = Tuple[str, float]
Result = Tuple[Benchmark, Data]

os.chdir(os.path.dirname(sys.argv[0]))
verbose = '--verbose' in sys.argv

vcy_exe = '../veracity/src/vcy.exe'
infer_dir = 'benchmarks/inferred/'
infer_loop_dir = 'benchmarks/inferred_loops/'
output_dir = 'benchmarks/inference_output/'

class VcyError(Exception):
    def __init__(self, msg) -> None:
        super().__init__(msg)
        self.msg = msg

def filesInDir(d):
    return [d + f for f in os.listdir("../veracity/" + d) if os.path.isfile(os.path.join("../veracity/" + d, f))]

# Program name, followed by any command line arguments
benchmarks : List[Benchmark] = \
    filesInDir('benchmarks/test/')
    #filesInDir(infer_dir) + filesInDir(infer_loop_dir)

manual_results : List[Result] = [
    ("matrix", ("y0 = 0", 1.88)),
    ("nonlinear", ("w * x = 0 && z = 0", 25.59))
]

class Heuristic(Enum):
    # SIMPLE = 0
    POKE = 11
    POKE2 = 21
    # POKE2_LATTICE = 22
    MC_MAX = 31
    # MC_MAX_EARLY_TERM = 33
    # MC_MAX_LATTICE = 32
    # MC_MAX_POKE2 = 34
    # MC_BISECT = 41
    # MC_BISECT_LATTICE = 42
    
    def __str__(self):
        return string_of_heuristic[self]

string_of_heuristic = {
    # Heuristic.SIMPLE: "simple",
    Heuristic.POKE: "poke",
    Heuristic.POKE2: "poke2",
    # Heuristic.POKE2_LATTICE: "\\poketwo{}-lattice",
    Heuristic.MC_MAX: "mcmax",
    # Heuristic.MC_MAX_EARLY_TERM: "\\mcmax-earlyterm{}",
    # Heuristic.MC_MAX_LATTICE: "\\mcmax{}-lattice",
    # Heuristic.MC_MAX_POKE2: "mcmaxpoke2",
    # Heuristic.MC_BISECT: "mc-bisect",
    # Heuristic.MC_BISECT_LATTICE: "mc-bisect-lattice"
}

command_of_heuristic = {
    # Heuristic.SIMPLE: [],
    Heuristic.POKE: "--poke",
    Heuristic.POKE2: "--poke2",
    # Heuristic.POKE2_LATTICE: ["--poke2", "--lattice"],
    Heuristic.MC_MAX: "--mcpeak-max",
    # Heuristic.MC_MAX_EARLY_TERM: ["--mcpeak-max", "--mc-term", "0.75"],
    # Heuristic.MC_MAX_LATTICE: ["--mcpeak-max", "--lattice"],
    # Heuristic.MC_MAX_POKE2: "--mcpeak-max-poke2",
    # Heuristic.MC_BISECT: ["--mcpeak-bisect"],
    # Heuristic.MC_BISECT_LATTICE: ["--mcpeak-bisect", "--lattice"]
}

prover = ['cvc4', 'cvc5', 'z3']

def goodness(n_atoms, answer_incomplete):
    cmplx = int(n_atoms) >= 10
    if(answer_incomplete == "false"):
        if cmplx: return "complex complete"
        else: return "simple complete"
    else:
        if cmplx: return "complex incomplete"
        else: return "simple incomplete"

def run_benchmark(index : int, b : Benchmark, h, p) -> Result:
    prog = b
    if os.path.exists("test.lattice"):
        os.remove("test.lattice")
    if os.path.exists("test.equivc"):
        os.remove("test.equivc")
    command_infer = [vcy_exe, 'infer', '-q', '../veracity/' + prog, '--time', '-o', '../veracity/' + output_dir + os.path.basename(prog), '--timeout', '120', '--prover', p, command_of_heuristic[h]] # Time out in 2 minutes.

    def f(command : List[str]):
        popen = subprocess.Popen(
            command, universal_newlines=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        out, err = popen.communicate()
        if 'error' in err or 'exception' in err:
            raise VcyError(err.split('\n')[1])
        return out, err

    sys.stdout.write(f'{(index+1):#2d}/{len(benchmarks)} {prog} Finding inference... ')
    sys.stdout.flush()
    infer, output = f(command_infer)
    print(output)
    output = list(filter(None, output.split('\n')))
    time = output[len(output)-1]
    time_synth = float(output[len(output)-2])
    time_lattice_construct = float(output[len(output)-3])
    n_atoms = '-'.join(line.split(', ')[0] for line in output[0:len(output)-1])
    answer_incomplete = '-'.join(line.split(', ')[1] for line in output[0:len(output)-1])

    if verbose:
        sys.stdout.write(infer)

    sys.stdout.write(f'Done.\n')
    sys.stdout.flush()
    return b, (infer, float(time), float(time_synth), float(time_lattice_construct), n_atoms, answer_incomplete)

# https://texblog.net/latex-archive/uncategorized/symbols/
def latex_escape(s : str):
    s = s.replace('#', '\\#')
    s = s.replace('$', '\\$')
    s = s.replace('%', '\\%')
    s = s.replace('_', '\\_')
    s = s.replace('&', '\\&')
    s = s.replace('{', '\\{')
    s = s.replace('}', '\\}')
    s = s.replace('^', '\\^{}')
    s = s.replace('||', '\\textbar\\textbar\\ ')
    s = s.replace('>', '\\textgreater\\ ')
    s = s.replace('<', '\\textless\\ ')
    return s

def latex_of_result(r : Result) -> str:
    prog,data = r
    if data == [] :
        infer = ''
        n_atoms = -1
        good = 'error'
        time = -1
        time_synth = -1
        time_lattice_construct = -1
        return \
        f'{Path(prog).stem},' + \
        f'{time},' + \
        f'{time_synth},' + \
        f'{time_lattice_construct},' + \
        f'{n_atoms},' + \
        f'{good} '
    else:
        (infer,time,time_synth,time_lattice_construct,n_atoms,ans_incomplete) = data
        infer = infer.replace('\\', '')
        infer = ' '.join(s for s in infer.splitlines() if s)
        infer = latex_escape(infer)
        n_atoms = ' '.join(s for s in n_atoms.split('-') if s)
        ans_incomplete = ' '.join(s for s in ans_incomplete.split('-') if s)
        good = []
        for n in n_atoms.split(' '):
            i = 0
            good.append(goodness(n, ans_incomplete.split(' ')[i]))
            i = i + 1
        good = ' '.join(good)
    prog = latex_escape(prog)

    return \
        f'{Path(prog).stem},' + \
        f'{time:#.2f},' + \
        f'{time_synth:#.2f},' + \
        f'{time_lattice_construct:#.2f},' + \
        f'{n_atoms},' + \
        f'{good} '

    # f'\\texttt{{{infer}}} & ' + \

# latex_table_start = \
# r'''{\renewcommand{\arraystretch}{1.1}
# \begin{tabularx}{\columnwidth}{|l|c|X|c|c}
#     \hline
#     adt and test case,time,natoms,quality
#     \hline
# '''

latex_table_start = \
r'''adt and test case,time,natoms,quality
'''

# Program & Time (s) & Inference & n_atoms & Quality \\

# latex_table_end = \
# r'''
#     \hline
# \end{tabularx}}'''

latex_table_end = \
r''' '''

def build_table(rs : List[Result]) -> str:
    rows = "\n".join(map(latex_of_result, rs))
    return latex_table_start + rows + latex_table_end

def build_files():
    for h in string_of_heuristic:
        for p in prover:
            rs = []
            for i, b in enumerate(benchmarks):
                try:
                    rs.append(run_benchmark(i, b, h, p))
                except VcyError as err:
                    rs.append([b, []])
                    sys.stdout.write(f'\nFailure: {err.msg}\n')
            # rs.extend(manual_results)
            latex = build_table(list(rs))
            name = 'out-veracity-'+string_of_heuristic[h]+'-NoLatt-'+p+'-NoTermGen.csv'
            with open(name, 'w') as file:
                file.write(latex)

if __name__ == '__main__':
    build_files()
