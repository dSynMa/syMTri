
def create_nuxmv_model(name, vars, define, init, trans):
    text = "MODULE main\n"
    text += "VAR\n" + "\t" + ";\n\t".join(vars) + ";\n"
    text += "DEFINE\n" + "\t" + ";\n\t".join(define) + ";\n"
    text += "INIT\n" + "\t(" + ")\n\t& (".join(init) + ")\n"
    text += "TRANS\n" + "\t(" + ")\n\t& (".join(trans) + ")\n"
    text = text.replace("%", "mod")
    return text