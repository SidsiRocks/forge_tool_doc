from main import main,path_rel_to_script
import io

#TODO: figure out how to improve diff output here
# currently as the strings being compared are large the current way diff is
# displaced is not very useful
def test_addit_enc_transcr():
    cpsa_file_path = path_rel_to_script( "../additional_enc_test/addit_enc.rkt" )
    base_file_path = path_rel_to_script("./base_with_seq.frg")
    extra_func_file_path = path_rel_to_script( "./extra_funcs.frg" )
    run_forge_file_path = path_rel_to_script( "../additional_enc_test/addit_enc_run.frg" )

    destination_forge_file = io.StringIO()
    reference_transcription_file = path_rel_to_script( "../additional_enc_test/addit_new_transcr.frg" )

    with open(cpsa_file_path) as cpsa_file:
        with open(base_file_path) as base_file:
            with open(extra_func_file_path) as extra_func_file:
                with open(run_forge_file_path) as run_forge_file:
                    main(cpsa_file,destination_forge_file,base_file,extra_func_file,run_forge_file,False)

    destination_forge_file.seek(0)
    txt = destination_forge_file.read()
    destination_forge_file.close()

    with open(reference_transcription_file) as reference_file:
        correct_txt = reference_file.read()
        assert txt == correct_txt
