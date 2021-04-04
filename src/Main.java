import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

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

public class Main {
    public static void main(String[] args) throws ParseException, Exception {
        FileManager fm = FileManager.getInstance();
        fm.setSafeMode(false);
        fm.init();
        DataModel dm = setDataModelFromFile("resources\\vgu_dm.json");
        
        List<String> oclExp = Arrays.asList(
    		"TRUE"
    		,"caller = self"
    		,"caller.students->includes(self)"
    		,"Lecturer.allInstances()->forAll(l|Student.allInstances()->forAll(s|l.students->includes(s)))"
    		,"Lecturer.allInstances()->select(l|l = caller)->includes(self)"
    		,"Lecturer.allInstances()->forAll(l1|Lecturer.allInstances()->forAll(l2|l1.age = l2.age))"
    		,"Lecturer.allInstances()->forAll(l|l<>caller implies l.age < caller.age)"
        		);

        DM2MSFOL.setDataModel(dm);
        DM2MSFOL.map(fm);
        
        OCL2MSFOL.setDataModel(dm);
        // This is just for now.
        fm.commentln("Ad-hoc Contextual Model");
        OCL2MSFOL.putAdhocContextualSet("caller", "Lecturer");
        OCL2MSFOL.putAdhocContextualSet("self", "Lecturer");
        
        fm.commentln(oclExp.get(0));
        OCL2MSFOL.setExpression(oclExp.get(0));
        OCL2MSFOL.setLvalue(LogicValue.TRUE);
        OCL2MSFOL.map(fm);

        fm.checkSat();
        fm.close();
    }

    @SuppressWarnings("unused")
    private static List<String> readFromFile(String filePath) throws IOException {
        File file = new File(filePath);
        FileReader fileReader = new FileReader(file);
        BufferedReader bufferReader = new BufferedReader(fileReader);  //creates a buffering character input stream  
        String line;
        List<String> lines = new ArrayList<String>();
        
        while((line = bufferReader.readLine())!=null) {  
            lines.add(line); 
        }  
        fileReader.close(); 
        return lines;
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
