import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import org.vgu.dm2schema.dm.DataModel;
import org.vgu.se.smt.dm.DM2MSFOL;
import org.vgu.se.smt.file.FileManager;
import org.vgu.se.smt.logicvalue.LogicValue;
import org.vgu.se.smt.ocl.OCL2MSFOL;

/**************************************************************************
 * Copyright 2020 Vietnamese-German-University
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 * 
 * @author: ngpbh
 ***************************************************************************/

public class Runner {
    public static void main(String[] args) throws ParseException, Exception {
        FileManager fm = FileManager.getInstance();
        fm.setSafeMode(false);
        fm.open("resources//test.smt2");
        fm.init();
        
        DataModel dm = setDataModelFromFile("resources\\vgu_dm.json");
        DM2MSFOL.setDataModel(dm);
        DM2MSFOL.map2msfol(fm);
        
        OCL2MSFOL.setDataModel(dm);
        
//        Case 1: true
//        String inv = "true";
        
//        Case 2: caller.students->isEmpty
//        OCL2MSFOL.putAdhocContextualSet("caller", "Lecturer");
//        String inv = "caller.students->isEmpty()";
        
//        Case 3: self.age >= 18
        OCL2MSFOL.putAdhocContextualSet("self", "Student");
        String inv = "self.age >= 18";
        
//        Case 4: Student.allInstances()->forAll(s|s.lecturers->forAll(l|l.age > s.age))
//        String inv = "Student.allInstances()->forAll(s|s.lecturers->forAll(l|l.age > s.age))";

//        Case 5: caller.age = self.age
//        OCL2MSFOL.putAdhocContextualSet("self", "Student");
//        OCL2MSFOL.putAdhocContextualSet("caller", "Lecturer");
//        String inv = "caller.age = self.age";
        
//        Case 6, 7, 8: self.name = user
//        OCL2MSFOL.putAdhocContextualSet("self", "Student");
//        OCL2MSFOL.putAdhocContextualSet("user", "String");
//        String inv = "self.name = user";
        
        fm.commentln(inv);
        OCL2MSFOL.setExpression(inv);
        OCL2MSFOL.setLvalue(LogicValue.TRUE);
    	OCL2MSFOL.map2msfol(fm);
    	
    	fm.close();
    }

    private static DataModel setDataModelFromFile(String filePath)
        throws FileNotFoundException, IOException, ParseException, Exception {
        return transformToDataModel(filePath);
    }

    private static DataModel transformToDataModel(String dataModelURI)
        throws IOException, ParseException, FileNotFoundException, Exception {
        File dataModelFile = new File(dataModelURI);
        JSONArray dataModelJSONArray = (JSONArray) new JSONParser()
            .parse(new FileReader(dataModelFile));
        DataModel context = new DataModel(dataModelJSONArray);
        return context;
    }
}
