rm -f addit_new_transcr.frg
rm -f addit_transcr_seq.frg
python3 ../python_transcriber/main.py addit_enc.rkt addit_enc_run.frg --destination_forge_file_path addit_new_transcr.frg
python3 ../python_transcriber/transcribe_seq.py addit_enc.rkt addit_enc_run.frg addit_transcr_seq.frg
