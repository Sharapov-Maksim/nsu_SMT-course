package parser;

import java.util.List;
import parser.gen.SMTLIBv2BaseVisitor;
import parser.gen.SMTLIBv2Parser.ScriptContext;

public class SMTModelVisitor extends SMTLIBv2BaseVisitor<List<SMTCommand>> {

    @Override
    public List<SMTCommand> visitScript(ScriptContext ctx) {
        var commands = ctx.command().stream()
            .map(SMTModelKt::commandConstructor).toList();

        //var commands = new ArrayList<SMTCommand>(ctx.command().size());

        /*for (var com : ctx.command()) {
            if (com.cmd_setLogic() != null) {
                commands.add(new CmdSetLogic(com.symbol(0).getText()));
            } else {

            }
        }*/

        return commands;
    }
}
