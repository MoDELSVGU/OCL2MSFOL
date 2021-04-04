package org.vgu.se.smt.ocl;

import java.util.List;
import java.util.Map;
import java.util.Set;

import org.vgu.dm2schema.dm.DataModel;

import com.vgu.se.jocl.expressions.AssociationClassCallExp;
import com.vgu.se.jocl.expressions.BooleanLiteralExp;
import com.vgu.se.jocl.expressions.Expression;
import com.vgu.se.jocl.expressions.IntegerLiteralExp;
import com.vgu.se.jocl.expressions.IteratorExp;
import com.vgu.se.jocl.expressions.IteratorKind;
import com.vgu.se.jocl.expressions.LiteralExp;
import com.vgu.se.jocl.expressions.OclExp;
import com.vgu.se.jocl.expressions.OperationCallExp;
import com.vgu.se.jocl.expressions.PropertyCallExp;
import com.vgu.se.jocl.expressions.StringLiteralExp;
import com.vgu.se.jocl.expressions.Variable;
import com.vgu.se.jocl.expressions.VariableExp;
import com.vgu.se.jocl.utils.VariableUtils;

public class O2F_DefCVisitor extends OCL2MSFOLVisitor {

	public O2F_DefCVisitor(DataModel dm, Set<Variable> adhocContextualSet, Map<Expression, DefC> defC) {
		this.setDataModel(dm);
		this.setAdhocContextualSet(adhocContextualSet);
		this.defC = defC;
	}

	@Override
	public void visit(Expression exp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visit(IteratorExp iteratorExp) {
		switch (IteratorKind.valueOf(iteratorExp.getKind())) {
		case collect:
			break;
		case select:
			String newDefCName = "TEMP" + String.valueOf(defC.size());
			List<Variable> fVars = VariableUtils.FVars(iteratorExp);
			if (fVars.isEmpty()) {
			String arguments = "Classifier";
			DefC defCElement = new DefC();
			defCElement.nameDefinition = String.format("%s (%s) Bool", newDefCName, arguments);
			defCElement.nameApplied = String.format("(%s %s)", newDefCName, "%s");
			defC.put(iteratorExp, defCElement);
			String var = iteratorExp.getIterator().getName();
			String type = "Classifier";
			String template = Template.Def_c.select_1;
			String firstArgument = app(defCElement.nameApplied, fVars, var);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			Expression sourceExp = (OclExp) iteratorExp.getSource();
			List<Variable> fVarsSrc = VariableUtils.FVars(sourceExp);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(evalVisitor);
			String secondArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, var);

			Expression bodyExp = iteratorExp.getBody();
			trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(trueVisitor);
			String thirdArgument = trueVisitor.getFOLFormulae();

			defCElement.assertion = String.format(template, var, type, firstArgument, secondArgument, thirdArgument);
			} else {
//				String template = Template.Def_c.select_0;
			}
			break;
		default:
			break;
		}
	}

	@Override
	public void visit(OperationCallExp operationCallExp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visit(LiteralExp literalExp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visit(StringLiteralExp stringLiteralExp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visit(BooleanLiteralExp booleanLiteralExp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visit(IntegerLiteralExp integerLiteralExp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visit(PropertyCallExp propertyCallExp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visit(AssociationClassCallExp associationClassCallExp) {
		// TODO Auto-generated method stub

	}

	@Override
	public void visit(VariableExp variableExp) {
		// TODO Auto-generated method stub

	}

}