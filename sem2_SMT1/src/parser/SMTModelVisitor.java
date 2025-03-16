package parser;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import parser.gen.SMTLIBv2BaseVisitor;
import parser.gen.SMTLIBv2Parser.Cmd_setLogicContext;
import parser.gen.SMTLIBv2Parser.CommandContext;
import parser.gen.SMTLIBv2Parser.ScriptContext;

public class SMTModelVisitor extends SMTLIBv2BaseVisitor<List<SMTCommand>> {

    @Override
    public List<SMTCommand> visitScript(ScriptContext ctx) {
//        var commands = ctx.command().stream()
//            .map(x -> x.accept(this))
//            .flatMap(List::stream).toList();

        for (var com : ctx.command()) {
            com.accept(this);
        }


        return super.visitScript(ctx);
    }

    @Override
    public List<SMTCommand> visitCommand(CommandContext ctx) {




        return super.visitCommand(ctx);
    }

    @Override
    public List<SMTCommand> visitCmd_setLogic(Cmd_setLogicContext ctx) {

        return super.visitCmd_setLogic(ctx);
    }
}
