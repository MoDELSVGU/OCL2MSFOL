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

import java.util.Map;
import java.util.Set;

import org.vgu.dm2schema.dm.Attribute;
import org.vgu.dm2schema.dm.DataModel;
import org.vgu.dm2schema.dm.Entity;

import com.vgu.se.jocl.expressions.AssociationClassCallExp;
import com.vgu.se.jocl.expressions.BooleanLiteralExp;
import com.vgu.se.jocl.expressions.Expression;
import com.vgu.se.jocl.expressions.IntegerLiteralExp;
import com.vgu.se.jocl.expressions.IteratorExp;
import com.vgu.se.jocl.expressions.IteratorKind;
import com.vgu.se.jocl.expressions.LiteralExp;
import com.vgu.se.jocl.expressions.M2OAssociationClassCallExp;
import com.vgu.se.jocl.expressions.O2OAssociationClassCallExp;
import com.vgu.se.jocl.expressions.OperationCallExp;
import com.vgu.se.jocl.expressions.PropertyCallExp;
import com.vgu.se.jocl.expressions.StringLiteralExp;
import com.vgu.se.jocl.expressions.Variable;
import com.vgu.se.jocl.expressions.VariableExp;

public class O2F_EvalVisitor extends OCL2MSFOLVisitor {

    public O2F_EvalVisitor(DataModel dm, Set<Variable> adhocContextualSet, Map<Expression, DefC> defC) {
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
	    	defCVisitor = new O2F_DefCVisitor(dm,adhocContextualSet,defC);
	    	iteratorExp.accept(defCVisitor);
	    	String defCNameApplied = defC.get(iteratorExp).nameApplied;
	    	this.setFOLFormulae(String.format(defCNameApplied, "%s"));
	    	break;
		default:
			break;
		}
    }

    @Override
    public void visit(OperationCallExp operationCallExp) {
        switch (operationCallExp.getReferredOperation().getName()) {
        case "allInstances":
            String template = Template.Eval.allInstances;
            String clazz = operationCallExp.getSource().getType()
                .getReferredType();
            this.setFOLFormulae(String.format(template, clazz, "%s"));
            break;
        case "oclIsUndefined":
            break;
        case "oclIsKindOf":
            break;
        case "oclIsTypeOf":
            break;
        case "oclAsType":
            break;
        case "=":
        case "<>":
        case "<=":
        case ">=":
        case ">":
        case "<":
        case "and":
        case "or":
            break;
        case "not":
            break;
        case "implies":
            break;
        case "size":
            break;
        case "isEmpty":
            break;
        case "notEmpty":
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
        String template = Template.Eval.intLiteral;
        this.setFOLFormulae(String.format(template,
            Integer.toString(integerLiteralExp.getValue())));
    }

    @Override
    public void visit(PropertyCallExp propertyCallExp) {
        String property = propertyCallExp.getReferredProperty();
        String clazz = null;
        for (Entity e : dm.getEntities().values()) {
            for (Attribute att : e.getAttributes()) {
                if (att.getName().equals(property)) {
                    clazz = e.getName();
                }
            }
        }
        evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
        Expression exp = propertyCallExp.getNavigationSource();
        exp.accept(evalVisitor);
        String template = Template.Eval.attribute;
        this.setFOLFormulae(String.format(template, property,
            evalVisitor.getFOLFormulae(), clazz));
    }

    @Override
    public void visit(AssociationClassCallExp associationClassCallExp) {
        if (associationClassCallExp instanceof O2OAssociationClassCallExp) {
            String association = associationClassCallExp.getAssociation();
            String clazz = associationClassCallExp
                .getReferredAssociationEndType().getReferredType();
            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            Expression exp = associationClassCallExp.getNavigationSource();
            exp.accept(evalVisitor);
            String template = Template.Eval.association_0_1_arity;
            this.setFOLFormulae(String.format(template, association,
                evalVisitor.getFOLFormulae(), clazz));
        } else if (associationClassCallExp instanceof M2OAssociationClassCallExp
            && ((M2OAssociationClassCallExp) associationClassCallExp)
                .isOneEndAssociationCall()) {
            String association = associationClassCallExp.getAssociation();
            String clazz = associationClassCallExp
                .getReferredAssociationEndType().getReferredType();
            evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            Expression exp = associationClassCallExp.getNavigationSource();
            exp.accept(evalVisitor);
            String template = Template.Eval.association_0_1_arity;
            this.setFOLFormulae(String.format(template, association,
                evalVisitor.getFOLFormulae(), clazz));
        } else {
        	String association = associationClassCallExp.getAssociation();
        	String template = Template.Eval.association_n_arity;
        	evalVisitor = new O2F_EvalVisitor(dm,adhocContextualSet,defC);
            Expression exp = associationClassCallExp.getNavigationSource();
            exp.accept(evalVisitor);
            this.setFOLFormulae(String.format(template, association,
                    "%s"));
        }
    }

    @Override
    public void visit(VariableExp variableExp) {
        String template = Template.Eval.variable;
        this.setFOLFormulae(
            String.format(template, variableExp.getVariable().getName()));
    }
}
