import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import org.vgu.dm2schema.dm.DataModel;
import org.vgu.se.smt.dm.DM2MSFOL;
import org.vgu.se.smt.file.FileManager;
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
        DataModel dm = setDataModelFromFile("resources\\dm_fol.json");

        DM2MSFOL.setDataModel(dm);
        DM2MSFOL.map(fm);

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
