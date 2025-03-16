package smt.parser;

import java.util.List;
import smt.parser.gen.SMTLIBv2BaseVisitor;
import smt.parser.gen.SMTLIBv2Parser.ScriptContext;

public class SMTModelVisitor extends SMTLIBv2BaseVisitor<List<SMTCommand>> {

    @Override
    public List<SMTCommand> visitScript(ScriptContext ctx) {
        var commands = ctx.command().stream()
            .map(SMTFormatModelKt::commandConstructor).toList();

        return commands;
    }
}
