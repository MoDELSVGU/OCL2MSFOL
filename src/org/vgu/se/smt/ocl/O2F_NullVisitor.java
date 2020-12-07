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
import com.vgu.se.jocl.expressions.Variable;
import com.vgu.se.jocl.expressions.VariableExp;
import com.vgu.se.jocl.utils.VariableUtils;

public class O2F_NullVisitor extends OCL2MSFOLVisitor {

    public O2F_NullVisitor(DataModel dm) {
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
            String template = Template.Null.forAll;

            String var = iteratorExp.getIterator().getName();
            String type = "Classifier";

            OclExp sourceExp = (OclExp) iteratorExp.getSource();
            List<Variable> fVarsSrc = VariableUtils.FVars(sourceExp);
            invalVisitor = new O2F_InvalidVisitor(dm);
            sourceExp.accept(invalVisitor);
            String firstArgument = invalVisitor.getFOLFormulae();

            evalVisitor = new O2F_EvalVisitor(dm);
            sourceExp.accept(evalVisitor);
            String secondArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc,
                var);

            Expression bodyExp = iteratorExp.getBody();
            nullVisitor = new O2F_NullVisitor(dm);
            bodyExp.accept(nullVisitor);
            String thirdArgument = nullVisitor.getFOLFormulae();

            falseVisitor = new O2F_FalseVisitor(dm);
            sourceExp.accept(falseVisitor);
            String forthArgument = falseVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument, var, type,
                secondArgument, thirdArgument, forthArgument));
            break;
        case first:
            break;
        case flatten:
            break;
        case forAll:
            template = Template.Null.forAll;

            var = iteratorExp.getIterator().getName();
            type = "Classifier";

            sourceExp = (OclExp) iteratorExp.getSource();
            fVarsSrc = VariableUtils.FVars(sourceExp);
            invalVisitor = new O2F_InvalidVisitor(dm);
            sourceExp.accept(invalVisitor);
            firstArgument = invalVisitor.getFOLFormulae();

            evalVisitor = new O2F_EvalVisitor(dm);
            sourceExp.accept(evalVisitor);
            secondArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc,
                var);

            bodyExp = iteratorExp.getBody();
            nullVisitor = new O2F_NullVisitor(dm);
            bodyExp.accept(nullVisitor);
            thirdArgument = nullVisitor.getFOLFormulae();

            trueVisitor = new O2F_TrueVisitor(dm);
            sourceExp.accept(trueVisitor);
            forthArgument = trueVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument, var, type,
                secondArgument, thirdArgument, forthArgument));
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
            String template = Template.Null.allInstances;
            this.setFOLFormulae(template);
            break;
        case "oclIsUndefined":
            template = Template.Null.oclIsUndefined;
            this.setFOLFormulae(template);
            break;
        case "oclIsInvalid":
            template = Template.Null.oclIsInvalid;
            this.setFOLFormulae(template);
            break;
        case "oclIsKindOf":
            template = Template.Null.oclIsKindOf;
            this.setFOLFormulae(template);
            break;
        case "oclIsTypeOf":
            template = Template.Null.oclIsTypeOf;
            this.setFOLFormulae(template);
            break;
        case "oclAsType":
            break;
        case "=":
            template = Template.Null.equality;
            this.setFOLFormulae(template);
            break;
        case "<>":
            template = Template.Null.inequality;
            this.setFOLFormulae(template);
            break;
        case "<=":
        case ">=":
        case ">":
        case "<":
        case "and":
            template = Template.Null.and;

            Expression exp = operationCallExp.getSource();
            Expression argExp = operationCallExp.getArguments().get(0);

            nullVisitor = new O2F_NullVisitor(dm);
            exp.accept(nullVisitor);
            String firstArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            String secondArgument = nullVisitor.getFOLFormulae();
            trueVisitor = new O2F_TrueVisitor(dm);
            exp.accept(trueVisitor);
            String thirdArgument = trueVisitor.getFOLFormulae();
            argExp.accept(trueVisitor);
            String forthArgument = trueVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument));
            break;
        case "or":
            template = Template.Null.or;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);

            nullVisitor = new O2F_NullVisitor(dm);
            exp.accept(nullVisitor);
            firstArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            secondArgument = nullVisitor.getFOLFormulae();
            falseVisitor = new O2F_FalseVisitor(dm);
            exp.accept(falseVisitor);
            thirdArgument = falseVisitor.getFOLFormulae();
            argExp.accept(falseVisitor);
            forthArgument = falseVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument));
            break;
        case "not":
            template = Template.Null.not;
            exp = operationCallExp.getArguments().get(0);
            nullVisitor = new O2F_NullVisitor(dm);
            exp.accept(nullVisitor);
            this.setFOLFormulae(
                String.format(template, nullVisitor.getFOLFormulae()));
            break;
        case "implies":
            template = Template.Null.implies;

            exp = operationCallExp.getSource();
            argExp = operationCallExp.getArguments().get(0);
            nullVisitor = new O2F_NullVisitor(dm);
            exp.accept(nullVisitor);
            firstArgument = nullVisitor.getFOLFormulae();
            argExp.accept(nullVisitor);
            secondArgument = nullVisitor.getFOLFormulae();
            falseVisitor = new O2F_FalseVisitor(dm);
            exp.accept(falseVisitor);
            String fifthArgument = falseVisitor.getFOLFormulae();
            argExp.accept(falseVisitor);
            forthArgument = falseVisitor.getFOLFormulae();
            trueVisitor = new O2F_TrueVisitor(dm);
            exp.accept(trueVisitor);
            String sixthArgument = trueVisitor.getFOLFormulae();
            argExp.accept(trueVisitor);
            thirdArgument = trueVisitor.getFOLFormulae();

            this.setFOLFormulae(String.format(template, firstArgument,
                secondArgument, thirdArgument, forthArgument, fifthArgument,
                sixthArgument));
            break;
        case "size":
            break;
        case "isEmpty":
            template = Template.Null.isEmpty;
            this.setFOLFormulae(template);
            break;
        case "notEmpty":
            template = Template.Null.notEmpty;
            this.setFOLFormulae(template);
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
        String template = Template.Null.intLiteral;
        this.setFOLFormulae(template);
    }

    @Override
    public void visit(PropertyCallExp propertyCallExp) {
        String template = Template.Null.attribute;
        evalVisitor = new O2F_EvalVisitor(dm);
        propertyCallExp.accept(evalVisitor);
        String type = propertyCallExp.getType().getReferredType();
        this.setFOLFormulae(String.format(template, evalVisitor.getFOLFormulae(), nullOf(type)));
    }

    @Override
    public void visit(AssociationClassCallExp associationClassCallExp) {
        // TODO Auto-generated method stub

    }

    @Override
    public void visit(VariableExp variableExp) {
        String template = Template.Null.variable;
        String var = variableExp.getVariable().getName();
        String type = variableExp.getType().getReferredType();
        this.setFOLFormulae(String.format(template,var,nullOf(type)));
    }
}