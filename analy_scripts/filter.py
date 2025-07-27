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
    data=data["rounds"]
    path, fname=os.path.split(file)
    if not os.path.exists(path) and path!="":
        os.mkdir(path)
    if path!="":
        d=path+"/"+fname.split(".")[0]+"_analy.json"
    else:
        d=fname.split(".")[0]+"_analy.json"
    dic={}
    for r in data.keys():
        dic[r]={}
        out=data[r]["data_reports"]
        for name in out.keys():
            distilled=out[name]["task_reports"]["execute_proof_gen"]
            if distilled["scores"]["proof"]["can_compile"]:
                if distilled["extra_info"]["refined_times"]>1:
                    dic[r][name]={"history":distilled["extra_info"]["history"], "final_proof": {"imports": distilled["artifact"]["imports"],"proof_aux": distilled["artifact"]["proof_aux"],"proof": distilled["artifact"]["proof"]}}
    with open(d,"w") as f:
        json.dump(dic,f, indent=4)


if __name__ == "__main__":
    typer.run(main)