package org.vgu.se.smt.file;
import java.io.FileWriter;
import java.io.IOException;

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

public final class FileManager {
    private static String fileName = "resources\\test.smt2";
    private static FileWriter fileWriter;
    private static final FileManager INSTANCE = new FileManager();
    
    private FileManager() {}

    public static FileManager getInstance() {
        return INSTANCE;
    }

    public void close() throws IOException {
        fileWriter.close();
    }
    
    public void open() throws IOException {
        fileWriter = new FileWriter(fileName);
    }
    
    public void writeln(String content) throws IOException {
        fileWriter.write(content);
        fileWriter.write("\n");
    }

    public void init() throws IOException {
        open();
        writeln("(set-logic UFSLIA)");
        writeln("(set-option :produce-models true)");
        writeln("(declare-sort Classifier 0)");
        writeln("(declare-const nullClassifier Classifier)");
        writeln("(declare-const nullInteger Int)");
        writeln("(declare-const nullString String)");
    }

    public void checkSat() throws IOException {
        writeln("(check-sat)");
    }
}
