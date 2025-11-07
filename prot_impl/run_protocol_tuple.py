import os
import subprocess
import argparse
from pathlib import Path

# TODO use a basic makefile for this instead maybe

def path_rel_to_script(path):
    script_path = Path(__file__).parent
    return (script_path / path).resolve()

if __name__ == "__main__":
    new_python_transcribe_main = path_rel_to_script( "../cspa_expanding/python_transcriber/main_tuple.py")
    # python_transcriber_seq_main = path_rel_to_script("../cspa_expanding/python_transcriber/transcribe_seq.py")

    parser = argparse.ArgumentParser(prog="run_protocol",description="small helper script to run protocol")
    parser.add_argument("folder_path")
    args = parser.parse_args()

    base_prot_name = None
    file_names = [f for f in os.listdir(args.folder_path) if os.path.join(args.folder_path,f)]

    rkt_file = [f for f in file_names if f.endswith(".rkt")]
    if len(rkt_file) != 1:
        print(f"expected one rkt_file in folder not {rkt_file}")
        exit(-1)
    base_prot_name = rkt_file[0][:-4]
    rkt_file = os.path.join(args.folder_path,rkt_file[0])

    forge_file_name = base_prot_name + ".frg"
    print(f"forge_file_name = {forge_file_name}")
    forge_file_name = [f for f in file_names if f == forge_file_name ]
    if len(forge_file_name) != 1:
        print(f"expected one run file in folder not {forge_file_name}")
        exit(-1)
    forge_file_name = os.path.join(args.folder_path, forge_file_name[0] )

    file_suffix = "tuple_new_transcr.frg"
    destination_forge_file_path = os.path.join(args.folder_path,f"{base_prot_name}_{file_suffix}")
    new_transcribe_cmd = f"python3 {new_python_transcribe_main} {rkt_file} {forge_file_name} --destination_forge_file_path {destination_forge_file_path}"
    print(f"new_transcribe_cmd = {new_transcribe_cmd}")
    subprocess.run(new_transcribe_cmd,shell=True)
    # print(f"old_transcribe_cmd = {old_transcribe_cmd}")
    # subprocess.run(old_transcribe_cmd,shell=True)

