package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import kodkod.ast.BinaryExpression;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntToExprCast;
import kodkod.ast.Relation;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.ExprCompOperator;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;

public class GuignaSimplifier extends Simplifier {

    private A4Solution solution;
    private A4Reporter reporter;
    private boolean printDump;

    public GuignaSimplifier(boolean printDump) {
        super();
        this.printDump = printDump;
    }

    @Override
    public boolean simplify(A4Reporter rep, A4Solution sol,
            List<Formula> formulas) throws Err {

        this.reporter = rep;
        this.solution = sol;

        for (Formula formula : formulas) {
            formula.toString();
            guigna_simplify(formula);
        }

        boolean ans = super.simplify(rep, sol, formulas);
        
        if(this.printDump)
            System.out.println(sol.getBounds().toString());

        return ans;
    }

    private Tuple intExprToTuple(IntConstant intConstant) {
        Object atom = "" + intConstant.value();
        return solution.getFactory().tuple(atom);
    }

    private void guigna_simplify(Formula formula) throws Err {
        if (formula instanceof ComparisonFormula) {
            ComparisonFormula comparision = (ComparisonFormula) formula;
            Expression left = comparision.left();
            Expression right = comparision.right();
            if (left instanceof Relation
                    && comparision.op().equals(
                            ExprCompOperator.SUBSET)
                    && right instanceof BinaryExpression) {
                Relation relation = (Relation) left;
                try {
                    List<Tuple> guignaIntConstraint = getGuignaIntConstraint(right);
                    if (!guignaIntConstraint.isEmpty()) {

                        boolean findLower = false;
                        boolean makeInmutable = false;
                        TupleSet lower = solution.query(findLower, relation,
                                makeInmutable);

                        boolean findUpper = true;
                        boolean makeMutable = true;
                        TupleSet upper = solution.query(findUpper, relation,
                                makeMutable);

                        List<Tuple> upper_tuples = new LinkedList<Tuple>();
                        for (Tuple tuple: upper) {
                            upper_tuples.add(tuple);
                        }

                        for (Tuple tuple : upper_tuples) {
                            if (!guignaIntConstraint.contains(tuple)) {
                                upper.remove(tuple);
                            }
                        }
                        solution.shrink(relation, lower, upper);

                        reporter.debug("Comment: Guigna integer bound shrink " + relation.toString() + " " + upper_tuples.size() + "->"
                                + upper.size() + "\n");
                    }
                } catch (NotAGuignaConstraintExpression e) {

                }
                relation.toString();
            }

        }

    }

    private static class NotAGuignaConstraintExpression extends Exception {
    }

    private List<Tuple> getGuignaIntConstraint(Expression expr)
            throws NotAGuignaConstraintExpression {
        if (expr instanceof BinaryExpression) {
            BinaryExpression binExpr = (BinaryExpression) expr;
            if (binExpr.op().equals(ExprOperator.PRODUCT)) {
                Expression product_left = binExpr.left();
                if (product_left.arity() != 1)
                    throw new NotAGuignaConstraintExpression();

                product_left.toString();

                if (product_left instanceof Relation) {
                    Relation relation = (Relation) product_left;
                    TupleSet approx = solution.approximate(relation);
                    if (approx.size() != 1)
                        throw new NotAGuignaConstraintExpression();

                    Tuple from_tuple = approx.iterator().next();

                    Expression product_right = binExpr.right();
                    if (product_right instanceof IntToExprCast) {
                        IntToExprCast intToExprCast = (IntToExprCast) product_right;
                        if (intToExprCast.intExpr() instanceof IntConstant) {
                            IntConstant intConstant = (IntConstant) intToExprCast
                                    .intExpr();
                            Tuple to_tuple = intExprToTuple(intConstant);

                            Tuple product_tuple = from_tuple.product(to_tuple);

                            return Collections.singletonList(product_tuple);

                        } else
                            throw new NotAGuignaConstraintExpression();
                    } else
                        throw new NotAGuignaConstraintExpression();
                } else
                    throw new NotAGuignaConstraintExpression();

            } else if (binExpr.op().equals(ExprOperator.UNION)) {
                List<Tuple> left = getGuignaIntConstraint(binExpr.left());
                List<Tuple> right = getGuignaIntConstraint(binExpr
                        .right());
                List<Tuple> result = new LinkedList<Tuple>();
                result.addAll(left);
                result.addAll(right);
                return result;
            } else
                throw new NotAGuignaConstraintExpression();
        } else
            throw new NotAGuignaConstraintExpression();
    }
}
