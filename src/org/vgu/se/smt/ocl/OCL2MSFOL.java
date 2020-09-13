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

import org.vgu.dm2schema.dm.DataModel;
import org.vgu.se.smt.file.FileManager;

import com.vgu.se.jocl.exception.OclParserException;
import com.vgu.se.jocl.expressions.Expression;
import com.vgu.se.jocl.expressions.OclExp;
import com.vgu.se.jocl.parser.simple.SimpleParser;

public class OCL2MSFOL {
    
    private static DataModel dm;
    private static OclExp exp;
    
    public static void setExpression(String string) {
        SimpleParser simpleParser = new SimpleParser();
        Expression exp_ = simpleParser.parse(string, dm);
        if(exp_ instanceof OclExp)
            exp = (OclExp) exp_;
        throw new OclParserException();
    }
    
    public static void setDataModel(DataModel dm_) {
        dm = dm_;
    }
    
    public static void map(FileManager fm) {
        
    }
    
}
