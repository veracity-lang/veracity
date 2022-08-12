python3 "./infer_verif_gen.py"
python3 "./speedup_gen.py" test 4
python3 "./speedup_gen.py" "test/filesystem" 4 "../veracity/benchmarks/case-studies/filesystem.vcy"
python3 "./speedup_gen.py" "test/crowdfund" 4 "../veracity/benchmarks/case-studies/crowdfund.vcy"
