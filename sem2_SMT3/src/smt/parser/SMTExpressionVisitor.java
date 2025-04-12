package smt.parser;

import java.util.List;
import smt.parser.Expression.FunApp;
import smt.parser.Expression.Identifier;
import smt.parser.gen.SMTLIBv2BaseVisitor;
import smt.parser.gen.SMTLIBv2Parser.Qual_identifierContext;
import smt.parser.gen.SMTLIBv2Parser.TermContext;

public class SMTExpressionVisitor extends SMTLIBv2BaseVisitor<Expression> {

    @Override
    public Expression visitTerm(TermContext ctx) {

        Identifier id;
        if (ctx.qual_identifier() != null) {
            id = (Identifier) ctx.qual_identifier().accept(this);
        } else {
            throw new UnsupportedOperationException(ctx.getText());
        }

        // supported cases:
        // | qual_identifier
        // | ParOpen qual_identifier term+ ParClose
        if (ctx.term().size() > 0) {
            List<Expression> args = ctx.term().stream()
                .map(termContext -> termContext.accept(this))
                .toList();
            return new FunApp(id, args);
        } else {
            assert (ctx.var_binding() == null || ctx.var_binding().isEmpty());
            assert (ctx.sorted_var() == null || ctx.sorted_var().isEmpty());
            assert (ctx.match_case() == null || ctx.match_case().isEmpty());
            assert (ctx.attribute() == null || ctx.attribute().isEmpty());
            return id;
        }
    }

    @Override
    public Expression visitQual_identifier(Qual_identifierContext ctx) {
        String text = ctx.identifier().getText();
        assert (!text.isEmpty());
        return new Identifier(text);
    }
}
