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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.vgu.dm2schema.dm.DataModel;
import org.vgu.se.smt.file.FileManager;
import org.vgu.se.smt.logicvalue.LogicValue;

import com.vgu.se.jocl.expressions.Expression;
import com.vgu.se.jocl.expressions.OclExp;
import com.vgu.se.jocl.expressions.Variable;
import com.vgu.se.jocl.parser.simple.SimpleParser;
import com.vgu.se.jocl.types.Type;

public class OCL2MSFOL {

	private static DataModel dm;
	private static OclExp exp;
	private static LogicValue lvalue;
	private static Set<Variable> adhocContextualSet = new HashSet<>();
	private static Map<Expression, DefC> defC = new HashMap<Expression, DefC>();

	public static void setExpression(String string) {
		SimpleParser simpleParser = new SimpleParser();
		adhocContextualSet.forEach(simpleParser::putAdhocContextualSet);
		Expression exp_ = simpleParser.parse(string, dm);
		if (exp_ instanceof OclExp)
			exp = (OclExp) exp_;
	}

	public static void putAdhocContextualSet(String vName, String vType) {
		Variable v = new Variable(vName, new Type(vType));
		adhocContextualSet.remove(v);
		adhocContextualSet.add(v);
	}

	public static void setDataModel(DataModel dm_) {
		dm = dm_;
	}

	public static void map(FileManager fm) throws IOException {
		OCL2MSFOLVisitor visitor;

//		for (Variable v : adhocContextualSet) {
//			fm.writeln(String.format("(declare-const %s %s)", v.getName(), "Classifier"));
//			fm.writeln(String.format("(assert (%s %s))", v.getType(), v.getName()));
//		}
		
		defC = new HashMap<Expression, DefC>();

		if (lvalue == LogicValue.INVALID) {
			visitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
		} else if (lvalue == LogicValue.FALSE) {
			visitor = new O2F_FalseVisitor(dm, adhocContextualSet, defC);
		} else if (lvalue == LogicValue.NULL) {
			visitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
		} else {
			visitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
		}
		exp.accept(visitor);
		
		for (DefC d : defC.values()) {
			fm.writeln(String.format("(declare-fun %s)", d.nameDefinition));
			fm.assertln(d.assertion);
		}
		
		fm.assertln(visitor.getFOLFormulae());
	}

	public static LogicValue getLvalue() {
		return lvalue;
	}

	public static void setLvalue(LogicValue lvalue) {
		OCL2MSFOL.lvalue = lvalue;
	}
}
