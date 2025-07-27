import typer
import json
import os

def main(file: str):
    with open(file,"r") as f:
        data=json.load(f)
    # way to access: rounds -> [round_number] -> data_reports -> [case_name] -> task_reports -> execute_proof_gen
    # -> artifact -> proof / proof_aux / imports
    # -> extra_info
    # -> scores -> proof -> can_compile / error
    leanpath="./datasets/"
    path=file.split(".")[0]+"_lean"
    if not os.path.exists(path) and path!="":
        os.mkdir(path)
    for rounds in data.keys():
        for name in data[rounds].keys():
            d=data[rounds][name]
            fname=f"{name}_round_{rounds}.lean"
            wname=f"{name}_round_{rounds}_failed.lean"
            with open(leanpath+name+"/task.lean","r") as f:
                lean_temp=f.read()
            out1=lean_temp.split("sorry")[0]+d["final_proof"]["proof"]+"\n--- proof_aux"+d["final_proof"]["proof_aux"]

            out2=lean_temp.split("sorry")[0]+d["history"]["refinement_1"]["output"]["proof"]+"\n--- proof_aux"+d["history"]["refinement_1"]["output"]["proof_aux"]+"\n\n--- with error:\n"+d["history"]["refinement_1"]["error"]
            # out=out+"\n\n\n\n--- the following is the first attempt:\n\n--- Error"+d["history"]["refinement_1"]["error"]
            # out=out+"\n--- proof_aux:"+d["history"]["refinement_1"]["output"]["proof_aux"]+"\n--- proof:"+d["history"]["refinement_1"]["output"]["proof"]
            with open(path+"/"+fname,"w") as f:
                f.write(out1)
            with open(path+"/"+wname,"w") as f:
                f.write(out2)


if __name__ == "__main__":
    typer.run(main)