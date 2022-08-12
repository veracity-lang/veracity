#!/usr/bin/env python3

import subprocess
import sys, os
from os.path import abspath
from pathlib import Path
from typing import Tuple, List
import re

vcy_dir = '../'
paper_dir = '../../veracity-paper/semantics/'

vcy_exe = vcy_dir + 'src/vcy.exe'

target_file_infer = paper_dir + 'inference_table.tex'
target_file_infer_apx = paper_dir + 'inference_table_unabridged.tex'
target_file_verif = paper_dir + 'verify_table.tex'

# Timeout in seconds
timeout = 120

### Types

class ResultInfer: pass
class ResultInferNA(ResultInfer): pass
class ResultInferFail(ResultInfer): pass
class ResultInferComplex(ResultInfer): pass
class ResultInferTime(ResultInfer):
    t : float

class ResultVerif: pass
class ResultVerifNA(ResultVerif): pass
class ResultVerifFail(ResultVerif): pass

class ResultVerifSucceed(ResultVerif):
    t : float
    def __init__(self, _t=-1):
        self.t = _t

class ResultVerifCorrectComplete(ResultVerifSucceed): pass
class ResultVerifCorrectIncomplete(ResultVerifSucceed): pass
class ResultVerifCorrectUnknown(ResultVerifSucceed): pass
class ResultVerifIncorrect(ResultVerifSucceed): pass


ResultPhis = List[str]
TResultInfer = Tuple[str, ResultInfer, ResultPhis]
TResultVerif = Tuple[str, str, ResultVerif]

ColumnData = List[Tuple[str,str]]

class VcyError(Exception):
    def __init__(self, msg) -> None:
        super().__init__(msg)
        self.msg = msg


benchmark_dir = vcy_dir + 'benchmarks/'

infer_dir        = benchmark_dir + 'inferred/'
infer_loop_dir   = benchmark_dir + 'inferred_loops/'
infer_manual_dir = benchmark_dir + 'manual/'
output_dir       = benchmark_dir + 'inference_output/'
verif_dir       = benchmark_dir + 'verify/'

def files_in_dir(d):
    return [
        d + f for f in os.listdir(d) 
        if os.path.isfile(d + f)
    ]

if __name__ == '__main__':
    os.chdir(os.path.dirname(sys.argv[0]))

    infer_benchmarks : List[str] = \
        files_in_dir(infer_dir) + files_in_dir(infer_loop_dir)

    manual_benchmarks : List[str] = \
        files_in_dir(infer_manual_dir)

    verif_benchmarks : List[str] = \
        files_in_dir(verif_dir)

### Symbols

symbol_verif_correct = '\\benchcorrect'
symbol_verif_incorrect = '\\benchincorrect'
symbol_unknown = '\\benchunknown'
symbol_complete = '\\benchcorrect'
symbol_incomplete = '\\benchincorrect'
symbol_failure = '\\benchfailure'
symbol_not_applicable = '\\benchna'
symbol_complex = '\\benchcplx'



infer_table_cols : ColumnData = [ 
    ('l', 'Program'), 
    ('r', 'Time (s)'), 
    ('X', 'Inferred Conditions')
]

verif_table_cols : ColumnData = [
    ('l', 'Program'),
    ('r', 'Time (s)'),
    ('r', 'Verified?'),
    ('r', 'Complete?'),
    ('X', 'Provided Condition')
]



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
    s = s.replace('> ', '\\textgreater\\ ')
    s = s.replace('< ', '\\textless\\ ')
    return s



def latex_table_header(cd : ColumnData) -> str:
    return \
        '{\\renewcommand{\\arraystretch}{\\benchtablerowstretch}\\footnotesize\n' + \
        '\\begin{tabularx}{\\columnwidth}{|' + '|'.join(c for c,_ in cd) + '|}\n' + \
        '\t\\hline\n' + \
        '\t' + ' & '.join(n for _,n in cd) + ' \\\\\n' + \
        '\t\\hline\n' + \
        '\t\\hline\n'

latex_table_footer = \
    '\n\t\\hline\n\\end{tabularx}}'


def result_infer_of_output (output : str, time : str) -> Tuple[ResultInfer,ResultPhis]:
    lines = output.splitlines()
    if len(lines) == 0:
        return ResultInferNA(), []

    try:
        t = float(time)
    except ValueError:
        raise Exception(f"Could not parse time as float: '{time}'")

    r = ResultInferTime()
    r.t = t
    return r, lines

    

## TODO assumes there's only one verification
def result_verif_of_output (output : str, time : str) -> Tuple[str,ResultVerif]:
    lines = output.splitlines()
    if len(lines) == 0:
        return "", ResultVerifNA()

    try:
        t = float(time)
    except ValueError:
        raise Exception(f"Could not parse time as float: '{time}'")

    if lines[1] == 'correct':
        if len(lines) == 2:
            raise Exception('Missing completeness result')
        if lines[2] == 'true':
            r = ResultVerifCorrectComplete()
        elif lines[2] == 'false':
            r = ResultVerifCorrectIncomplete()
        elif lines[2] == 'unknown':
            r = ResultVerifCorrectUnknown()
        else:
            raise Exception(f"Failed to parse complete output '{lines[2]}'")
    elif lines[1] == 'incorrect':
        r = ResultVerifIncorrect()
    else:
        raise Exception(f"Failed to parse verif output '{lines[1]}'")

    r.t = t
    return lines[0], r



def run_command(command : List[str]):
    popen = subprocess.Popen(
        command, universal_newlines=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    out, err = popen.communicate()
    if 'error' in err or 'exception' in err:
        raise VcyError(err.split('\n')[1])
    return out, err

def run_benchmark_infer(index : int, total : int, prog : str) -> TResultInfer:
    command_infer = [
        vcy_exe, 'infer', '-q', '--time', 
        '-o', '../veracity/' + output_dir + os.path.basename(prog), 
        '--timeout', str(timeout), '--prover', 'cvc5', 
        vcy_dir + prog 
    ]

    sys.stdout.write(f'Infer {(index+1):#2d}/{total} {prog} ...')
    sys.stdout.flush()
    try:
        infer, time = run_command(command_infer)
        result_infer, result_phis = result_infer_of_output(infer, time)
    except VcyError as err:
        result_infer = ResultInferFail()
        result_phis = []
        sys.stdout.write(f'\nFailure: {err.msg}\n')

    sys.stdout.write(f' Done.\n')
    sys.stdout.flush()

    return prog, result_infer, result_phis


def run_benchmark_verif(index : int, total : int, prog : str) -> TResultVerif:
    command_verif = [vcy_exe, 'verify', '-q', '--time', '--cond', vcy_dir + prog]
    
    sys.stdout.write(f'Verif {(index+1):#2d}/{total} {prog} ...')
    sys.stdout.flush()

    try:
        verif, time = run_command(command_verif)
        phi, result_verif = result_verif_of_output(verif, time)
    except VcyError as err:
        result_verif = ResultVerifFail()
        phi = ''
        sys.stdout.write(f'\nFailure: {err.msg}\n')
    
    sys.stdout.write(f' Done.\n')
    sys.stdout.flush()

    return prog, phi, result_verif


def latex_tt(s : str) -> str:
    return f'\\texttt{{{s}}}'

def latex_of_prog (prog : str) -> str:
    return latex_tt(Path(prog).stem)

def latex_of_time(t : float):
    return f'{t:#.2f}'

def latex_of_infer (infer : ResultInfer) -> str:
    if isinstance(infer, ResultInferNA):
        return symbol_not_applicable
    if isinstance(infer, ResultInferFail):
        return symbol_failure
    if isinstance(infer, ResultInferComplex):
        return symbol_complex
    if isinstance(infer, ResultInferTime):
        return latex_of_time(infer.t)
    raise Exception("Unexpected ResultInfer type")

def latex_of_verif (verif : ResultVerif) -> Tuple[str,str,str]:
    if isinstance(verif, ResultVerifNA):
        return symbol_not_applicable, symbol_not_applicable, symbol_not_applicable
    if isinstance(verif, ResultVerifFail):
        return symbol_not_applicable, symbol_failure, symbol_not_applicable
    if isinstance(verif, ResultVerifCorrectComplete):
        return latex_of_time(verif.t), symbol_verif_correct, symbol_complete
    if isinstance(verif, ResultVerifCorrectIncomplete):
        return latex_of_time(verif.t), symbol_verif_correct, symbol_incomplete
    if isinstance(verif, ResultVerifCorrectUnknown):
        return latex_of_time(verif.t), symbol_verif_correct, symbol_unknown
    if isinstance(verif, ResultVerifIncorrect):
        return latex_of_time(verif.t), symbol_verif_incorrect, symbol_not_applicable
    raise Exception("Unexpected ResultVerif type")



op_map = {
    '==': '!=',  '!=': '==',
    '<': '>=',   '>=': '<',
    '>': '<=',   '<=': '>'
}
op_map_escaped = {
    re.escape(k): re.escape(v) 
    for k,v in op_map.items()
}

re_ops = '|'.join(map(re.escape, op_map_escaped.keys()))
re_term = r'.*?'

re_neg_match = re.compile(
    fr''' ! \s? \( 
        \s? (?P<arg1>{re_term}) \s? 
        (?P<op>{re_ops}) \s? 
        (?P<arg2>{re_term}) \s? \) 
        ''',
    re.X
)

def re_neg_goal(r : re.Match) -> str:
    arg1 = r.group('arg1')
    op   = r.group('op')
    arg2 = r.group('arg2')
    res = f'{arg1} {op_map[op]} {arg2}'
    return res

## Replaces '!(_ op _)' with '_ !op _'
def latex_of_exp(exp : str, abridge=False) -> str:
    exp = re.sub(re_neg_match, re_neg_goal, exp)
    if abridge:
        l = exp.split('||')
        if len(l) > 2:
            exp = f'{l[0]}|| ... ||{l[-1]}'
    return exp

def latex_of_phis(phis : ResultPhis, abridge=False) -> str:
    if not phis:
        return symbol_not_applicable
    p = [latex_of_exp(e, abridge) for e in phis]
    p = '; '.join(p)
    p = latex_escape(p)
    p = latex_tt(p)
    return p

def latex_of_infer_result(r : TResultInfer, abridge=False) -> str:
    prog,infer,phis = r
    prog = latex_of_prog(prog)
    infer = latex_of_infer(infer)
    phis = latex_of_phis(phis, abridge)
    return f'\t{prog} & {infer} & {phis}\\\\'

def latex_of_verif_result(r : TResultVerif) -> str:
    prog,phi,verif = r
    t,v,c = latex_of_verif(verif)
    prog = latex_of_prog(prog)
    phi = latex_of_phis([phi])
    return f'\t{prog} & {t} & {v} & {c} & {phi}\\\\'


def sort_by_programs(r : list):
    r.sort(key = lambda t : os.path.basename(t[0]))

def build_table(rs : list, f_latex, cd : ColumnData) -> str:
    rows = '\n'.join(map(f_latex, rs))
    return latex_table_header(cd) + rows + latex_table_footer

def write_table(name : str, data : str):
    with open(name, 'w') as file:
        file.write(data)
        sys.stdout.write(f'Results written to {abspath(name)}\n')

def build_infer_file():
    rs : List[TResultInfer] = []
    for i, b in enumerate(infer_benchmarks):
        try:
            rs.append(run_benchmark_infer(i, len(infer_benchmarks), b))
        except Exception as e:
            sys.stderr.write(f'\nFailure: {str(e)}\n')

    for b in manual_benchmarks:
        sys.stdout.write(f'Adding manual {b}.\n')
        rs.append((b, ResultInferComplex(), []))

    sort_by_programs(rs)
    
    latex = build_table(list(rs), lambda r : latex_of_infer_result(r, True), infer_table_cols)
    write_table(target_file_infer, latex)

    latex = build_table(list(rs), latex_of_infer_result, infer_table_cols)
    write_table(target_file_infer_apx, latex)


def build_verif_file():
    rs : List[TResultVerif] = []
    for i, b in enumerate(verif_benchmarks):
        try:
            rs.append(run_benchmark_verif(i, len(verif_benchmarks), b))
        except Exception as e:
            sys.stderr.write(f'\nFailure: {str(e)}\n')

    sort_by_programs(rs)
    
    latex = build_table(list(rs), latex_of_verif_result, verif_table_cols)
    write_table(target_file_verif, latex)




if __name__ == '__main__':
    if '--verify' not in sys.argv:
        build_infer_file()
    if '--infer' not in sys.argv:
        build_verif_file()
