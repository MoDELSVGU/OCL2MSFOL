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

public class O2F_FalseVisitor extends OCL2MSFOLVisitor {

    public O2F_FalseVisitor(DataModel dm) {
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
            String template = Template.False.exists;

            String var = iteratorExp.getIterator().getName();
            String type = "Classifier";

            OclExp sourceExp = (OclExp) iteratorExp.getSource();
            List<Variable> fVarsSrc = VariableUtils.FVars(sourceExp);
            evalVisitor = new O2F_EvalVisitor(dm);
            sourceExp.accept(evalVisitor);
            String firstArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc,
                var);

            Expression bodyExp = iteratorExp.getBody();
            falseVisitor = new O2F_FalseVisitor(dm);
            bodyExp.accept(falseVisitor);
            String secondArgument = falseVisitor.getFOLFormulae();

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
            template = Template.False.forAll;

            var = iteratorExp.getIterator().getName();
            type = "Classifier";

            sourceExp = (OclExp) iteratorExp.getSource();
            fVarsSrc = VariableUtils.FVars(sourceExp);
            evalVisitor = new O2F_EvalVisitor(dm);
            sourceExp.accept(evalVisitor);
            firstArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc,
                var);

            bodyExp = iteratorExp.getBody();
            falseVisitor = new O2F_FalseVisitor(dm);
            bodyExp.accept(falseVisitor);
            secondArgument = falseVisitor.getFOLFormulae();

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
            break;
        case isUnique:
            break;
        case last:
            break;
        case notEmpty:
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
            String template = Template.False.oclIsUndefined;
            Expression exp = operationCallExp.getSource();
            nullVisitor = new O2F_NullVisitor(
                this.getDataModel());
            exp.accept(nullVisitor);
            invalVisitor = new O2F_InvalidVisitor(
                this.getDataModel());
            exp.accept(invalVisitor);
            this.setFOLFormulae(String.format(template,
                nullVisitor.getFOLFormulae(), invalVisitor.getFOLFormulae()));
            break;
        case "oclIsInvalid":
            template = Template.False.oclIsInvalid;
            exp = operationCallExp.getSource();
            invalVisitor = new O2F_InvalidVisitor(
                this.getDataModel());
            exp.accept(invalVisitor);
            this.setFOLFormulae(
                String.format(template, invalVisitor.getFOLFormulae()));
            break;
        case "oclIsKindOf":
            template = Template.False.oclIsKindOf;
            exp = operationCallExp.getSource();
            evalVisitor = new O2F_EvalVisitor(this.getDataModel());
            exp.accept(evalVisitor);
            Expression argExp = operationCallExp.getArguments().get(0);
            if (argExp instanceof TypeExp) {
                String typeToCheck;
                typeToCheck = ((TypeExp) argExp).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeToCheck));
            } else {
                String typeToCheck;
                typeToCheck = ((VariableExp) operationCallExp.getArguments()
                    .get(0)).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeToCheck));
            }
            break;
        case "oclIsTypeOf":
            template = Template.False.oclIsTypeOf;
            exp = operationCallExp.getSource();
            evalVisitor = new O2F_EvalVisitor(this.getDataModel());
            exp.accept(evalVisitor);
            argExp = operationCallExp.getArguments().get(0);
            if (argExp instanceof TypeExp) {
                String typeToCheck;
                typeToCheck = ((TypeExp) argExp).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeToCheck));
            } else {
                String typeToCheck;
                typeToCheck = ((VariableExp) operationCallExp.getArguments()
                    .get(0)).getType().getReferredType();
                this.setFOLFormulae(String.format(template,
                    evalVisitor.getFOLFormulae(), typeToCheck));
            }
            break;
        case "oclAsType":
            break;
        case "=":
            template = Template.False.equality;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);
            evalVisitor = new O2F_EvalVisitor(dm);
            exp.accept(evalVisitor);
            String firstArgument = evalVisitor.getFOLFormulae();
            argExp.accept(evalVisitor);
            String secondArgument = evalVisitor.getFOLFormulae();
            nullVisitor = new O2F_NullVisitor(dm);
            exp.accept(nullVisitor);
            String thirdArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            String forthArgument = nullVisitor.getFOLFormulae();
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
            template = Template.False.inequality;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);
            nullVisitor = new O2F_NullVisitor(dm);
            exp.accept(nullVisitor);
            firstArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            secondArgument = nullVisitor.getFOLFormulae();
            evalVisitor = new O2F_EvalVisitor(dm);
            exp.accept(evalVisitor);
            thirdArgument = evalVisitor.getFOLFormulae();
            argExp.accept(evalVisitor);
            forthArgument = evalVisitor.getFOLFormulae();
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
            template = Template.False.and;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            falseVisitor = new O2F_FalseVisitor(dm);
            exp.accept(falseVisitor);
            firstArgument = falseVisitor.getFOLFormulae();
            argExp.accept(falseVisitor);
            secondArgument = falseVisitor.getFOLFormulae();

            this.setFOLFormulae(
                String.format(template, firstArgument, secondArgument));
            break;
        case "or":
            template = Template.False.or;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            falseVisitor = new O2F_FalseVisitor(dm);
            exp.accept(falseVisitor);
            firstArgument = falseVisitor.getFOLFormulae();
            argExp.accept(falseVisitor);
            secondArgument = falseVisitor.getFOLFormulae();

            this.setFOLFormulae(
                String.format(template, firstArgument, secondArgument));
            break;
        case "not":
            template = Template.False.not;
            exp = operationCallExp.getArguments().get(0);
            trueVisitor = new O2F_TrueVisitor(dm);
            exp.accept(trueVisitor);
            this.setFOLFormulae(String.format(template, trueVisitor.getFOLFormulae()));
            break;
        case "implies":
            template = Template.False.implies;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            trueVisitor = new O2F_TrueVisitor(dm);
            exp.accept(trueVisitor);
            firstArgument = trueVisitor.getFOLFormulae();
            falseVisitor = new O2F_FalseVisitor(dm);
            argExp.accept(falseVisitor);
            secondArgument = falseVisitor.getFOLFormulae();

            this.setFOLFormulae(
                String.format(template, firstArgument, secondArgument));
            break;
        case "size":
            break;
        case "isEmpty":
            template = Template.False.isEmpty;

            exp = operationCallExp.getSource();
            String var = "x";
            String type = "Classifier";

            evalVisitor = new O2F_EvalVisitor(dm);

            List<Variable> fvExp = VariableUtils.FVars(exp);

            firstArgument = app(evalVisitor.getFOLFormulae(), fvExp, var);

            invalVisitor = new O2F_InvalidVisitor(dm);
            exp.accept(invalVisitor);
            secondArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, var, type,
                firstArgument, secondArgument));
            break;
        case "notEmpty":
            template = Template.False.notEmpty;

            exp = operationCallExp.getSource();
            var = "x";
            type = "Classifier";

            evalVisitor = new O2F_EvalVisitor(dm);

            fvExp = VariableUtils.FVars(exp);

            firstArgument = app(evalVisitor.getFOLFormulae(), fvExp, var);

            invalVisitor = new O2F_InvalidVisitor(dm);
            exp.accept(invalVisitor);
            secondArgument = invalVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, var, type,
                firstArgument, secondArgument));
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
