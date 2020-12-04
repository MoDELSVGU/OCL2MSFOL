/**************************************************************************
Copyright 2020 Vietnamese-German-University

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

import java.io.IOException;

import org.vgu.dm2schema.dm.DataModel;
import org.vgu.se.smt.file.FileManager;

import com.vgu.se.jocl.exception.OclParserException;
import com.vgu.se.jocl.expressions.AssociationClassCallExp;
import com.vgu.se.jocl.expressions.BooleanLiteralExp;
import com.vgu.se.jocl.expressions.Expression;
import com.vgu.se.jocl.expressions.IntegerLiteralExp;
import com.vgu.se.jocl.expressions.IteratorExp;
import com.vgu.se.jocl.expressions.LiteralExp;
import com.vgu.se.jocl.expressions.OclExp;
import com.vgu.se.jocl.expressions.OperationCallExp;
import com.vgu.se.jocl.expressions.PropertyCallExp;
import com.vgu.se.jocl.expressions.RealLiteralExp;
import com.vgu.se.jocl.expressions.StringLiteralExp;
import com.vgu.se.jocl.expressions.VariableExp;
import com.vgu.se.jocl.expressions.sql.functions.SqlFnCurdate;
import com.vgu.se.jocl.expressions.sql.functions.SqlFnTimestampdiff;
import com.vgu.se.jocl.parser.simple.SimpleParser;
import com.vgu.se.jocl.visit.ParserVisitor;

public class OCL2MSFOL {

    private static DataModel dm;
    private static OclExp exp;

    public static void setExpression(String string) {
        SimpleParser simpleParser = new SimpleParser();
        Expression exp_ = simpleParser.parse(string, dm);
        if (exp_ instanceof OclExp)
            exp = (OclExp) exp_;
        throw new OclParserException(
            "The OCL expression cannot be parsed! Maybe there is an error with it?");
    }

    public static void setDataModel(DataModel dm_) {
        dm = dm_;
    }

    public static void map(FileManager fm) throws IOException {
        O2F_TrueVisitor visitor = new O2F_TrueVisitor(dm);
        exp.accept(visitor);
        fm.writeln(visitor.getFOLFormulae());
    }
}
