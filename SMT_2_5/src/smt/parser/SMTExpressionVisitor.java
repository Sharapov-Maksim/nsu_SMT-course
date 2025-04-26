package smt.parser;

import java.util.List;
import smt.parser.Expression.DecimalConstant;
import smt.parser.Expression.FunApp;
import smt.parser.Expression.Identifier;
import smt.parser.gen.SMTLIBv2BaseVisitor;
import smt.parser.gen.SMTLIBv2Parser.DecimalContext;
import smt.parser.gen.SMTLIBv2Parser.NumeralContext;
import smt.parser.gen.SMTLIBv2Parser.Qual_identifierContext;
import smt.parser.gen.SMTLIBv2Parser.Spec_constantContext;
import smt.parser.gen.SMTLIBv2Parser.TermContext;

public class SMTExpressionVisitor extends SMTLIBv2BaseVisitor<Expression> {

    @Override
    public Expression visitTerm(TermContext ctx) {

        Identifier id;
        if (ctx.qual_identifier() != null) {
            Expression some = ctx.qual_identifier().accept(this);
            if (some instanceof DecimalConstant) {
                return some;
            } else {
                id = (Identifier) some;
            }
        } else if (ctx.spec_constant() != null) {
            return ctx.spec_constant().accept(this);
        } else {
            throw new UnsupportedOperationException(ctx.getText());
        }

        if (!ctx.term().isEmpty()) {
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
        if (isNumeric(text)) {
            return new DecimalConstant(Double.parseDouble(text));
        }
        return new Identifier(text);
    }

    public static boolean isNumeric(String strNum) {
        if (strNum == null) {
            return false;
        }
        try {
            double d = Double.parseDouble(strNum);
        } catch (NumberFormatException nfe) {
            return false;
        }
        return true;
    }

    @Override
    public Expression visitSpec_constant(Spec_constantContext ctx) {
        if (ctx.numeral() != null) {
            return ctx.numeral().accept(this);
        } else if (ctx.decimal() != null) {
            return ctx.decimal().accept(this);
        }
        return null;
    }

    @Override
    public Expression visitNumeral(NumeralContext ctx) {
        return new DecimalConstant(Integer.decode(ctx.Numeral().getText()).doubleValue());
    }

    @Override
    public Expression visitDecimal(DecimalContext ctx) {
        return new DecimalConstant(Double.parseDouble(ctx.getText()));
    }
}
