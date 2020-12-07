/**************************************************************************
Copyright 2020 ngpbh
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

@author: ngpbh
***************************************************************************/

package org.vgu.se.smt.ocl;

import java.util.List;

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
import com.vgu.se.jocl.expressions.TypeExp;
import com.vgu.se.jocl.expressions.Variable;
import com.vgu.se.jocl.expressions.VariableExp;
import com.vgu.se.jocl.utils.VariableUtils;

public class O2F_TrueVisitor extends OCL2MSFOLVisitor {

    public O2F_TrueVisitor(DataModel dm) {
        this.setDataModel(dm);
    }

    @Override
    public void visit(Expression exp) {
        // TODO Auto-generated method stub

    }

    @Override
    public void visit(IteratorExp iteratorExp) {
        switch (IteratorKind.valueOf(iteratorExp.getKind())) {
        case any:
            break;
        case asBag:
            break;
        case asOrderedSet:
            break;
        case asSequence:
            break;
        case asSet:
            break;
        case at:
            break;
        case collect:
            break;
        case count:
            break;
        case excludes:
            break;
        case excludesAll:
            break;
        case excluding:
            break;
        case exists:
            String template = Template.True.exists;

            String var = iteratorExp.getIterator().getName();
            String type = "Classifier";

            OclExp sourceExp = (OclExp) iteratorExp.getSource();
            List<Variable> fVarsSrc = VariableUtils.FVars(sourceExp);
            evalVisitor = new O2F_EvalVisitor(dm);
            sourceExp.accept(evalVisitor);
            String firstArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc,
                var);

            Expression bodyExp = iteratorExp.getBody();
            trueVisitor = new O2F_TrueVisitor(dm);
            bodyExp.accept(trueVisitor);
            String secondArgument = trueVisitor.getFOLFormulae();

            invalVisitor = new O2F_InvalidVisitor(dm);
            sourceExp.accept(invalVisitor);
            String thirdArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, var, type,
                firstArgument, secondArgument, thirdArgument));
            break;
        case first:
            break;
        case flatten:
            break;
        case forAll:
            template = Template.True.forAll;

            var = iteratorExp.getIterator().getName();
            type = "Classifier";

            sourceExp = (OclExp) iteratorExp.getSource();
            fVarsSrc = VariableUtils.FVars(sourceExp);
            evalVisitor = new O2F_EvalVisitor(dm);
            sourceExp.accept(evalVisitor);
            firstArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc,
                var);

            bodyExp = iteratorExp.getBody();
            trueVisitor = new O2F_TrueVisitor(dm);
            bodyExp.accept(trueVisitor);
            secondArgument = trueVisitor.getFOLFormulae();

            invalVisitor = new O2F_InvalidVisitor(dm);
            sourceExp.accept(invalVisitor);
            thirdArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, var, type,
                firstArgument, secondArgument, thirdArgument));
            break;
        case includes:
            break;
        case includesAll:
            break;
        case including:
            break;
        case indexOf:
            break;
        case isEmpty:
            template = Template.True.isEmpty;

            Expression exp = iteratorExp.getSource();
            var = "x";
            type = iteratorExp.getSource().getType().getElementType().getReferredType();

            evalVisitor = new O2F_EvalVisitor(dm);
            exp.accept(evalVisitor);
            List<Variable> fvExp = VariableUtils.FVars(exp);

            firstArgument = app(evalVisitor.getFOLFormulae(), fvExp, var);

            invalVisitor = new O2F_InvalidVisitor(dm);
            exp.accept(invalVisitor);
            secondArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, var, "Classifier",
                firstArgument, secondArgument));
            break;
        case isUnique:
            break;
        case last:
            break;
        case notEmpty:
            template = Template.True.notEmpty;

            exp = iteratorExp.getSource();
            var = "x";
            type = iteratorExp.getSource().getType().getElementType().getReferredType();

            evalVisitor = new O2F_EvalVisitor(dm);
            exp.accept(evalVisitor);
            fvExp = VariableUtils.FVars(exp);

            firstArgument = app(evalVisitor.getFOLFormulae(), fvExp, var);

            invalVisitor = new O2F_InvalidVisitor(dm);
            exp.accept(invalVisitor);
            secondArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, var, "Classifier",
                firstArgument, secondArgument));
            break;
        case one:
            break;
        case reject:
            break;
        case select:
            break;
        case size:
            break;
        case sortedBy:
            break;
        case sum:
            break;
        case union:
            break;
        default:
            break;
        }
    }

    @Override
    public void visit(OperationCallExp operationCallExp) {
        switch (operationCallExp.getReferredOperation().getName()) {
        case "allInstances":
            break;
        case "oclIsUndefined":
            String template = Template.True.oclIsUndefined;
            Expression exp = operationCallExp.getSource();
            nullVisitor = new O2F_NullVisitor(dm);
            exp.accept(nullVisitor);
            invalVisitor = new O2F_InvalidVisitor(dm);
            exp.accept(invalVisitor);
            this.setFOLFormulae(String.format(template,
                nullVisitor.getFOLFormulae(), invalVisitor.getFOLFormulae()));
            break;
        case "oclIsInvalid":
            template = Template.True.oclIsInvalid;
            exp = operationCallExp.getSource();
            invalVisitor = new O2F_InvalidVisitor(dm);
            exp.accept(invalVisitor);
            this.setFOLFormulae(
                String.format(template, invalVisitor.getFOLFormulae()));
            break;
        case "oclIsKindOf":
            template = Template.True.oclIsKindOf;
            exp = operationCallExp.getSource();
            evalVisitor = new O2F_EvalVisitor(dm);
            exp.accept(evalVisitor);
            Expression argExp = operationCallExp.getArguments().get(0);
            if (argExp instanceof TypeExp) {
                String typeToCheck;
                typeToCheck = ((TypeExp) argExp).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeOf(typeToCheck)));
            } else {
                String typeToCheck;
                typeToCheck = ((VariableExp) argExp).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeOf(typeToCheck)));
            }
            break;
        case "oclIsTypeOf":
            template = Template.True.oclIsTypeOf;
            exp = operationCallExp.getSource();
            evalVisitor = new O2F_EvalVisitor(dm);
            exp.accept(evalVisitor);
            argExp = operationCallExp.getArguments().get(0);
            if (argExp instanceof TypeExp) {
                String typeToCheck;
                typeToCheck = ((TypeExp) argExp).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeOf(typeToCheck)));
            } else {
                String typeToCheck;
                typeToCheck = ((VariableExp) argExp).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeOf(typeToCheck)));
            }
            break;
        case "oclAsType":
            break;
        case "=":
            template = Template.True.equality;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);
            nullVisitor = new O2F_NullVisitor(dm);
            exp.accept(nullVisitor);
            String firstArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            String secondArgument = nullVisitor.getFOLFormulae();
            evalVisitor = new O2F_EvalVisitor(dm);
            exp.accept(evalVisitor);
            String thirdArgument = evalVisitor.getFOLFormulae();
            argExp.accept(evalVisitor);
            String forthArgument = evalVisitor.getFOLFormulae();
            invalVisitor = new O2F_InvalidVisitor(dm);
            exp.accept(invalVisitor);
            String fifthArgument = invalVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            String sixthArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument, fifthArgument,
                sixthArgument));
            break;
        case "<>":
            template = Template.True.inequality;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);
            evalVisitor = new O2F_EvalVisitor(dm);
            exp.accept(evalVisitor);
            firstArgument = evalVisitor.getFOLFormulae();
            argExp.accept(evalVisitor);
            secondArgument = evalVisitor.getFOLFormulae();
            nullVisitor = new O2F_NullVisitor(dm);
            exp.accept(nullVisitor);
            thirdArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            forthArgument = nullVisitor.getFOLFormulae();
            invalVisitor = new O2F_InvalidVisitor(dm);
            exp.accept(invalVisitor);
            fifthArgument = invalVisitor.getFOLFormulae();
            argExp.accept(invalVisitor);
            sixthArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument, fifthArgument,
                sixthArgument));
            break;
        case "<=":
        case ">=":
        case ">":
        case "<":
        case "and":
            template = Template.True.and;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            trueVisitor = new O2F_TrueVisitor(dm);
            exp.accept(trueVisitor);
            firstArgument = trueVisitor.getFOLFormulae();
            argExp.accept(trueVisitor);
            secondArgument = trueVisitor.getFOLFormulae();

            this.setFOLFormulae(
                String.format(template, firstArgument, secondArgument));
            break;
        case "or":
            template = Template.True.or;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            trueVisitor = new O2F_TrueVisitor(dm);
            exp.accept(trueVisitor);
            firstArgument = trueVisitor.getFOLFormulae();
            argExp.accept(trueVisitor);
            secondArgument = trueVisitor.getFOLFormulae();

            this.setFOLFormulae(
                String.format(template, firstArgument, secondArgument));
            break;
        case "not":
            template = Template.True.not;
            exp = operationCallExp.getArguments().get(0);
            falseVisitor = new O2F_FalseVisitor(dm);
            exp.accept(falseVisitor);
            this.setFOLFormulae(
                String.format(template, falseVisitor.getFOLFormulae()));
            break;
        case "implies":
            template = Template.True.implies;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            falseVisitor = new O2F_FalseVisitor(dm);
            exp.accept(falseVisitor);
            firstArgument = falseVisitor.getFOLFormulae();
            trueVisitor = new O2F_TrueVisitor(dm);
            argExp.accept(trueVisitor);
            secondArgument = trueVisitor.getFOLFormulae();

            this.setFOLFormulae(
                String.format(template, firstArgument, secondArgument));
            break;
        case "size":
            break;
        case "isUnique":
            break;
        case "flatten":
            break;
        default:
            break;
        }
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
