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

import org.vgu.dm2schema.dm.DataModel;

import com.vgu.se.jocl.expressions.AssociationClassCallExp;
import com.vgu.se.jocl.expressions.BooleanLiteralExp;
import com.vgu.se.jocl.expressions.Expression;
import com.vgu.se.jocl.expressions.IntegerLiteralExp;
import com.vgu.se.jocl.expressions.IteratorExp;
import com.vgu.se.jocl.expressions.LiteralExp;
import com.vgu.se.jocl.expressions.OperationCallExp;
import com.vgu.se.jocl.expressions.PropertyCallExp;
import com.vgu.se.jocl.expressions.RealLiteralExp;
import com.vgu.se.jocl.expressions.StringLiteralExp;
import com.vgu.se.jocl.expressions.VariableExp;
import com.vgu.se.jocl.expressions.sql.functions.SqlFnCurdate;
import com.vgu.se.jocl.expressions.sql.functions.SqlFnTimestampdiff;

public class O2F_EvalVisitor extends OCL2MSFOLVisitor {
    
    public O2F_EvalVisitor(DataModel dm) {
        this.dm = dm;
    }

    @Override
    public void visit(Expression exp) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void visit(IteratorExp iteratorExp) {
        // TODO Auto-generated method stub
        
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
    public void visit(RealLiteralExp realLiteralExp) {
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

    @Override
    public void visit(SqlFnCurdate variableExp) {
        // TODO Auto-generated method stub
        
    }

    @Override
    public void visit(SqlFnTimestampdiff variableExp) {
        // TODO Auto-generated method stub
        
    }

}
