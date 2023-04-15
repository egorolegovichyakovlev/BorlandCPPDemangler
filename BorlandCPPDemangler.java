/*
 * This is free and unencumbered software released into the public domain.
 *
 * Anyone is free to copy, modify, publish, use, compile, sell, or
 * distribute this software, either in source code form or as a compiled
 * binary, for any purpose, commercial or non-commercial, and by any
 * means.
 *
 * In jurisdictions that recognize copyright laws, the author or authors
 * of this software dedicate any and all copyright interest in the
 * software to the public domain. We make this dedication for the benefit
 * of the public at large and to the detriment of our heirs and
 * successors. We intend this dedication to be an overt act of
 * relinquishment in perpetuity of all present and future rights to this
 * software under copyright law.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
 * OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
 * ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 *
 * For more information, please refer to <http://unlicense.org/>
*/

//A script to demangle Borland C++ and Delphi 4 names.
//Ghidra supports only adding C types to functions. If a C++ type is detected by the demangler, the function will receive a type substituted with "undefined4" instead.
//@category Symbol

import docking.*;
import ghidra.app.context.ProgramSymbolActionContext;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.listing.Data;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.listing.Variable;
import ghidra.program.model.listing.LocalVariable;
import ghidra.program.model.listing.LocalVariableImpl;
import ghidra.program.model.symbol.Symbol;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.data.*;
import ghidra.program.util.*;
import ghidra.util.exception.*;
import ghidra.program.model.mem.MemoryAccessException;

import ghidra.program.util.string.StringSearcher;
import ghidra.program.util.string.FoundStringCallback;
import ghidra.program.util.string.FoundString;
import ghidra.program.model.address.AddressSetView;

import ghidra.app.services.CodeViewerService;

import java.lang.String;
import java.lang.Character;
import java.util.ArrayList;

import java.nio.ByteBuffer;

import java.awt.*;

import javax.swing.*;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

public class BorlandCPPDemangler extends GhidraScript {

    private static final int TABLE_LIMIT = 36;
    private static final int LENGTH_LIMIT = 250;

    private static boolean EXTRA_PARAMS = false;
    private static boolean NOMODIFY = false;
    private static boolean DEBUG_MSGS = false;

    enum SymbolKind {
        FUNCTION,
        CONSTRUCTOR,
        DESTRUCTOR,
        OPERATOR,
        CONVERSION,
        DATA,
        THUNK,
        TPDSC,
        VTABLE,
        VRDF_THUNK,
        DYN_THUNK
    }

    enum ModifierUniq {
        QUALIFIED,
        TEMPLATE,
    }

    enum Modifier {
        VIRDEF_FLAG,
        FRIEND_LIST,
        CTCH_HNDL_TBL,
        OBJ_DEST_TBL,
        THROW_LIST,
        EXC_CTXT_TBL,
        LINKER_PROC,
    }

    enum VTableFlag {
        HUGE,
        FASTTHIS,
        RTTI
    }

    private boolean prevTemplClose = false;

    private ArrayList<VTableFlag> vtblFlags = new ArrayList<VTableFlag>();

    private ArrayList<String> thunkArguments = new ArrayList<String>();

    private SymbolKind functionSymbolKind = null;

    private Modifier functionModifier = null;

    private ArrayList<ModifierUniq> functionUniqModifiers = new ArrayList<ModifierUniq>();


    private int charToSkip = -1;

    private Function demangleFunc = null;

    private char[] funcNameChars;

    private String funcName = new String();

    private String funcNamePart = new String();

    private ArrayList<String> mainArgumentsList = new ArrayList<String>();

    private String outputString = new String();

    private int charPtr = 0;

    private int kindFlag = 0;

    private String returnType = new String();

    private String callConvent = new String();

    private String regConvent = new String();

    private String flagsList = new String();

    private String onErrorReturn = new String();

    private boolean returnSuccess = true;


    private JFrame mainFrame;

    public class NameError extends Exception {
        public NameError(String errorMessage) {
            super(errorMessage);
        }
    }

    public class NameEnded extends Exception {
        public NameEnded(String errorMessage) {
            super(errorMessage);
        }
    }

    private void printDebug(String message) {
        if (DEBUG_MSGS == true) {
            println("[DEBUG]: " + message);
        }
    }

    @Override
    public void run() throws Exception {
        mainFrame = new JFrame("Borland C++ Function Demangler");
        mainFrame.setMinimumSize(new Dimension(350, 200));
        mainFrame.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);

        JPanel mainPanel = new JPanel();

        JButton demangleSingleFunctionButton = new JButton("Demangle single function");
        demangleSingleFunctionButton.setAlignmentX(demangleSingleFunctionButton.CENTER_ALIGNMENT);
        demangleSingleFunctionButton.setAlignmentY(demangleSingleFunctionButton.CENTER_ALIGNMENT);
        demangleSingleFunctionButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent arg0) {
                demangleSingle();
            }
        });

        JButton demangleAllFunctionsButton = new JButton("Demangle all functions");
        demangleAllFunctionsButton.setAlignmentX(demangleAllFunctionsButton.CENTER_ALIGNMENT);
        demangleAllFunctionsButton.setAlignmentY(demangleAllFunctionsButton.CENTER_ALIGNMENT);
        demangleAllFunctionsButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent arg0) {
                demangleAll();
            }
        });


        JButton findRTTIFunctionsButton = new JButton("Check strings for RTTI function names");
        findRTTIFunctionsButton.setAlignmentX(findRTTIFunctionsButton.CENTER_ALIGNMENT);
        findRTTIFunctionsButton.setAlignmentY(findRTTIFunctionsButton.CENTER_ALIGNMENT);
        findRTTIFunctionsButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent arg0) {
                searchStringsForRTTI();
            }
        });


        JCheckBox checkExtParams = new JCheckBox("Print extended parameters");
        checkExtParams.setAlignmentX(checkExtParams.CENTER_ALIGNMENT);
        checkExtParams.setAlignmentY(checkExtParams.CENTER_ALIGNMENT);
        checkExtParams.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                JCheckBox source = (JCheckBox)e.getSource();
                EXTRA_PARAMS = source.isSelected();
            }
        });


        JCheckBox checkNoModify = new JCheckBox("Don't modify functions (only print names)");
        checkNoModify.setAlignmentX(checkNoModify.CENTER_ALIGNMENT);
        checkNoModify.setAlignmentY(checkNoModify.CENTER_ALIGNMENT);
        checkNoModify.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                JCheckBox source = (JCheckBox)e.getSource();
                NOMODIFY = source.isSelected();
            }
        });

        JCheckBox checkShowVerbose = new JCheckBox("Show verbose logs (lots of output)");
        checkShowVerbose.setAlignmentX(checkShowVerbose.CENTER_ALIGNMENT);
        checkShowVerbose.setAlignmentY(checkShowVerbose.CENTER_ALIGNMENT);
        checkShowVerbose.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                JCheckBox source = (JCheckBox)e.getSource();
                DEBUG_MSGS = source.isSelected();
            }
        });

        Box innerBox = new Box(BoxLayout.Y_AXIS);
        innerBox.add(Box.createVerticalGlue());
        innerBox.add(demangleSingleFunctionButton);
        innerBox.add(demangleAllFunctionsButton);
        innerBox.add(findRTTIFunctionsButton);
        innerBox.add(checkExtParams);
        innerBox.add(checkNoModify);
        innerBox.add(checkShowVerbose);
        innerBox.add(Box.createVerticalGlue());

        mainFrame.add(innerBox);

        mainFrame.pack();

        mainFrame.setVisible(true);

    }

    private void searchStringsForRTTI() {
        int RTTITransaction = currentProgram.startTransaction("Search strings for Borland function names");

        StringSearcher searchForStrings = new StringSearcher(currentProgram, 5, 1, true, true);
        AddressSetView searcherAddress = searchForStrings.search(null, callbackString, true, monitor);

        currentProgram.endTransaction(RTTITransaction, true);
    }

    private FoundStringCallback callbackString = new FoundStringCallback() {
        @Override
        public void stringFound(FoundString foundString) {
            String gotString = foundString.getString(currentProgram.getMemory());
            Address gotAddress = foundString.getAddress();
            try {
                Address funcPointerAddress = currentProgram.getAddressFactory().getDefaultAddressSpace().getAddress(gotAddress.getOffset() - 8);
                Address funcAddress = currentProgram.getAddressFactory().getDefaultAddressSpace().getAddress(currentProgram.getMemory().getInt(funcPointerAddress));
                Address checkMagicAddress = currentProgram.getAddressFactory().getDefaultAddressSpace().getAddress(gotAddress.getOffset() - 44);
                Function foundFunc = currentProgram.getFunctionManager().getFunctionAt(funcAddress);
                int foundIsMagic = currentProgram.getMemory().getInt(checkMagicAddress);
                if (foundIsMagic == 0x00300003) {
                    if (NOMODIFY == false) {
                        String filteredName = gotString.replace(" ", "");
                        if (foundFunc == null) {
                            foundFunc = createFunction(funcAddress, filteredName);
                        } else {
                            try {
                                foundFunc.setName(filteredName, SourceType.IMPORTED);
                            } catch (DuplicateNameException exc) {
                            } catch (InvalidInputException exc) {
                                printerr("Function name could not be set (illegal characters): " + filteredName);
                            }
                        }
                    }

                    println("Found function \"" + gotString + "\" at " + funcAddress.toString());
                }

            } catch (MemoryAccessException exc) {}
        }
    };

    private void demangleAll() {
        int demangleTransaction = currentProgram.startTransaction("Demangle multiple Borland functions");
        FunctionIterator funList = currentProgram.getListing().getFunctions(true);
        while (funList.hasNext()) {
            Function toDemangle = funList.next();
            String funName = toDemangle.getName();
            if (funName.startsWith("@")) {
                println("\"" + funName + "\" -> \"" + demangleBorlandFunction(toDemangle) + "\"");
            }
        }
        currentProgram.endTransaction(demangleTransaction, true);
    }

    private void demangleSingle() {
        int demangleTransaction = currentProgram.startTransaction("Demangle single Borland function");

        CodeViewerService codeViewer = state.getTool().getService(CodeViewerService.class);
        ProgramLocation location = codeViewer.getCurrentLocation();
        Address address = location.getAddress();

        Function funAddr = getFunctionAt(address);

        println("\"" + funAddr.getName() + "\" -> \"" + demangleBorlandFunction(funAddr) + "\"");
        currentProgram.endTransaction(demangleTransaction, true);
    }

    private void flushDemangler() {

        functionSymbolKind = null;

        functionModifier = null;

        functionUniqModifiers = new ArrayList<ModifierUniq>();

        charToSkip = -1;

        funcNameChars = null;

        funcName = new String();

        funcNamePart = new String();

        mainArgumentsList = new ArrayList<String>();

        outputString = new String();

        charPtr = 0;

        kindFlag = 0;

        thunkArguments = new ArrayList<String>();

        vtblFlags = new ArrayList<VTableFlag>();

        returnType = new String();

        callConvent = new String();

        regConvent = new String();

        flagsList = new String();

        onErrorReturn = new String();

        returnSuccess = true;

    }

    private String demangleBorlandFunction(Function borlandFun) {

        demangleFunc = borlandFun;

        if (borlandFun == null) {
            printerr("No function selected!");
            return "";
        }

        String returnDemangled = demangleBorlandString(borlandFun.getName());

        if (returnDemangled == null) {
            return "";
        }

        if (NOMODIFY == false) {
            String filteredFuncName = funcNamePart.replace("(", "").replace(")", "").replace("[", "").replace("]", "");

            if (filteredFuncName.startsWith("operator ")) {
                filteredFuncName = filteredFuncName.replaceFirst("operator ", "");
            }

            if (filteredFuncName.contains(" operator ")) {
                filteredFuncName = filteredFuncName.replace(" operator ", "");
            }

            if (filteredFuncName.startsWith("__closure ")) {
                filteredFuncName = filteredFuncName.replaceFirst("__closure ", "");
            }

            if (filteredFuncName.contains(" __closure ")) {
                filteredFuncName = filteredFuncName.replace(" __closure ", "");
            }

            filteredFuncName = filteredFuncName.replace(" ", "");


            try {
                borlandFun.setName(filteredFuncName, SourceType.IMPORTED);
            } catch (DuplicateNameException exc) {
            } catch (InvalidInputException exc) {
                printerr("Function name could not be set (illegal characters): " + filteredFuncName);
            }
        }


        String funConvent = borlandFun.getCallingConventionName();

        if (callConvent == "__cdecl" || callConvent == "__fastcall" || callConvent == "__stdcall") {
            funConvent = callConvent;
        }

        DataType retTypeData = findDataType(returnType);

        printDebug("Calling convention detected: " + funConvent);

        printDebug("Return type detected: " + retTypeData.getName() + " -- " + returnType);


        Variable retTypeVariable = borlandFun.getReturn();

        try {
            DataType undefData = new Undefined4DataType();
            if (retTypeData.isEquivalent(undefData) == false) {
                retTypeVariable.setDataType(retTypeData, SourceType.IMPORTED);
            }

        } catch (InvalidInputException exc) {
        }


        int stackOffsetVal = retTypeData.getLength();

        int funCounter = 0;

        ArrayList<Variable> localParamsNew = new ArrayList<Variable>();

        while (funCounter < mainArgumentsList.size()) {
            DataType argTypeData = findDataType(mainArgumentsList.get(funCounter));

            Variable argVar = null;

            try {
                argVar = new LocalVariableImpl("param_" + (funCounter+1), argTypeData, stackOffsetVal, currentProgram);

                localParamsNew.add(argVar);

                printDebug("Argument " + funCounter + " \"" + argTypeData.getName() + "\" - \"" + mainArgumentsList.get(funCounter) + "\"");

                stackOffsetVal += argTypeData.getLength();
            } catch (InvalidInputException exc) {
            }

            funCounter += 1;

        }


        if (returnSuccess == true && NOMODIFY == false) {
            try {
                borlandFun.updateFunction(
                    funConvent,
                    retTypeVariable,
                    localParamsNew,
                    Function.FunctionUpdateType.CUSTOM_STORAGE,
                    false,
                    SourceType.IMPORTED
                );

            } catch (InvalidInputException exc) {
            } catch (DuplicateNameException exc) {
            }

        }

        String extraParams = new String();

        boolean isQualified = false;

        boolean isTemplate = false;

        int modifiersLen = 0;

        while (modifiersLen < functionUniqModifiers.size()) {
            switch (functionUniqModifiers.get(modifiersLen)) {
                case QUALIFIED:
                    isQualified = true;
                    break;

                case TEMPLATE:
                    isTemplate = true;
                    break;
            }
            modifiersLen += 1;
        }

        if (isQualified == true) {
            extraParams += "qualified ";
        }

        if (isTemplate == true) {
            extraParams += "template ";
        }

        if (functionModifier != null) {
            switch (functionModifier) {
                case VIRDEF_FLAG:
                    extraParams += "virdef_flag ";
                    break;
                case FRIEND_LIST:
                    extraParams += "friend_list ";
                    break;
                case CTCH_HNDL_TBL:
                    extraParams += "catch_handler_table ";
                    break;
                case OBJ_DEST_TBL:
                    extraParams += "object_destructor_table ";
                    break;
                case THROW_LIST:
                    extraParams += "throw_list ";
                    break;
                case EXC_CTXT_TBL:
                    extraParams += "exception_context_table ";
                    break;
            }
        }

        if (functionSymbolKind != null) {
            switch (functionSymbolKind) {
                case FUNCTION:
                    extraParams += "function";
                    break;
                case CONSTRUCTOR:
                    extraParams += "constructor";
                    break;
                case DESTRUCTOR:
                    extraParams += "destructor";
                    break;
                case OPERATOR:
                    extraParams += "operator";
                    break;
                case CONVERSION:
                    extraParams += "conv_operator";
                    break;
                case DATA:
                    extraParams += "data";
                    break;
                case THUNK:
                    extraParams += "thunk";
                    break;
                case TPDSC:
                    extraParams += "typedesc";
                    break;
                case VTABLE:
                    extraParams += "vtable";
                    break;
                case VRDF_THUNK:
                    extraParams += "virdef_thunk";
                    break;
            }
        }

        demangleFunc = null;

        if (EXTRA_PARAMS == true) {
            returnDemangled = extraParams + " " + returnDemangled;
        }

        return returnDemangled;
    }

    private String demangleBorlandString(String name) {

        flushDemangler();

        boolean errorDetected = false;

        String returnString = new String();

        if (name.charAt(0) != '@') {

            printerr("Function is not mangled!");
            return null;

        } else {

            funcName = name.substring(1, name.length());

        }

        String[] allSplits = name.split("@");

        char[] allPart = name.toCharArray();

        char[] allPartReverse = name.toCharArray();

        char[] lastPart = allSplits[allSplits.length-1].toCharArray();

        boolean notMsPart = false;

        if (lastPart.length > 1) {

            for (int chPart = 0; chPart < lastPart.length; chPart += 1) {
                if (Character.isDigit(lastPart[chPart]) == false) {
                    notMsPart = true;
                }
            }

        } else {

            notMsPart = true;

        }

        if (notMsPart == false) {
            printerr("Function is Microsoft mangled!");
            return null;
        }

        boolean isPascal = true;

        for (int i = allPart.length-1; i >= 0; i -= 1) {
            if (allPart[i] >= 'a' && allPart[i] <= 'z') {
                isPascal = false;
                break;
            }
        }

        if (isPascal == true) {
            funcName = funcName.toLowerCase();
        } else {
            printDebug("Not pascal");
        }

        funcNameChars = funcName.toCharArray();

        try {

            returnString += copyName(false, true, -1);

            if  (functionSymbolKind == SymbolKind.TPDSC || functionModifier != null) {

                /* Previous name */
                String[] spaceSplit = returnString.split(" ");
                returnString = spaceSplit[spaceSplit.length-1];

            }

            if  (functionSymbolKind == SymbolKind.CONSTRUCTOR || functionSymbolKind == SymbolKind.DESTRUCTOR) {

                String[] qualsList = returnString.split("::");

                String qualLast = qualsList[qualsList.length-1];

                if  (functionSymbolKind == SymbolKind.DESTRUCTOR) {
                    returnString += "~";
                }

                returnString += qualLast;
            }

            printDebug("After name copied: " + returnString);

            funcNamePart = returnString;

            boolean doArgs = true;


            /* Copy arguments */

            if  (thisChar() == '$' && doArgs == true) {
                char charHoldNext;

                charHoldNext = nextChar();
                if (charHoldNext != 'q' && charHoldNext != 'x' && charHoldNext != 'w') {
                    printerr("Symbol parsing failed: wrong argument character sequence at " + charPtr);
                    return null;
                }

                returnString += copyType(false, true);

                if (functionSymbolKind == null) {
                    functionSymbolKind = SymbolKind.FUNCTION;
                }

            } else if (functionSymbolKind == null) {

                functionSymbolKind = SymbolKind.DATA;

            } else if (vtblFlags.isEmpty() == false) {

                String vtblString = new String();

                for (int i = 0; i < vtblFlags.size(); i += 1) {

                    if (vtblString.length() > 0) {
                        vtblString += ", ";
                    }

                    switch (vtblFlags.get(i)) {
                        case HUGE:
                            vtblString += "huge";
                            break;
                        case FASTTHIS:
                            vtblString += "fastthis";
                            break;
                        case RTTI:
                            vtblString += "rtti";
                            break;
                    }

                }

                returnString += " (" + vtblString + ")";

            }


        } catch (NameError err) {
            printerr("Name error: " + err.getMessage());
            printerr("Name which errored: @" + funcName);
            errorDetected = true;
            returnString += onErrorReturn+"...";
            printerr(returnString);
            returnSuccess = false;
        }

        if (errorDetected == false) {

            if (returnType.isEmpty() == false) {
                returnString = returnType + " " + returnString;
            }

            if (callConvent.isEmpty() == false) {
                returnString = callConvent + " " + returnString;
            }

            if (regConvent.isEmpty() == false) {
                returnString = regConvent + " " + returnString;
            }

            if (flagsList.isEmpty() == false) {
                returnString = flagsList + returnString;
            }

        }

        return returnString;

    }

    private DataType findDataType(String typeToFind) {
        DataType typeToReturn = new Undefined4DataType();

        String argText = typeToFind;
        String mainArg = argText;

        if (mainArg.startsWith("operator ")) {
            mainArg = mainArg.replaceFirst("operator ", "");
        }

        if (mainArg.contains(" operator ")) {
            mainArg = mainArg.replace(" operator ", "");
        }

        if (mainArg.startsWith("__closure ")) {
            mainArg = mainArg.replaceFirst("__closure ", "");
        }

        if (mainArg.contains(" __closure ")) {
            mainArg = mainArg.replace(" __closure ", "");
        }


        if (mainArg.startsWith("const ")) {
            mainArg = mainArg.replaceFirst("const ", "");
        }
        if (mainArg.startsWith("volatile ")) {
            mainArg = mainArg.replaceFirst("volatile ", "");
        }

        String argType = new String();

        boolean isUnsigned = false;

        if (mainArg.startsWith("unsigned ")) {
            mainArg = mainArg.replaceFirst("unsigned ", "");
            isUnsigned = true;
        } else if (mainArg.startsWith("signed ")) {
            mainArg = mainArg.replaceFirst("signed ", "");
        }

        if (mainArg.startsWith("char")) {
            mainArg = mainArg.replaceFirst("char", "");
            argType = "char";
            typeToReturn = new CharDataType();
            if (isUnsigned == true) {
                argType = "u" + argType;
                typeToReturn = new UnsignedCharDataType();
            }

        } else if (mainArg.startsWith("void")) {
            mainArg = mainArg.replaceFirst("void", "");
            typeToReturn = new VoidDataType();
            argType = "void";
        } else if (mainArg.startsWith("wchar_t")) {
            mainArg = mainArg.replaceFirst("wchar_t", "");
            typeToReturn = new WideCharDataType();
            argType = "wchar_t";
        } else if (mainArg.startsWith("short")) {
            mainArg = mainArg.replaceFirst("short", "");
            argType = "short";
            typeToReturn = new ShortDataType();
            if (isUnsigned == true) {
                argType = "u" + argType;
                typeToReturn = new UnsignedShortDataType();
            }

        } else if (mainArg.startsWith("int")) {
            mainArg = mainArg.replaceFirst("int", "");
            argType = "int";
            typeToReturn = new IntegerDataType();
            if (isUnsigned == true) {
                argType = "u" + argType;
                typeToReturn = new UnsignedIntegerDataType();
            }

        } else if (mainArg.startsWith("long long")) {
            mainArg = mainArg.replaceFirst("long long", "");
            argType = "longlong";
            typeToReturn = new LongLongDataType();
            if (isUnsigned == true) {
                argType = "u" + argType;
                typeToReturn = new UnsignedLongLongDataType();
            }


        } else if (mainArg.startsWith("long")) {
            mainArg = mainArg.replaceFirst("long", "");
            argType = "long";
            typeToReturn = new LongDataType();
            if (isUnsigned == true) {
                argType = "u" + argType;
                typeToReturn = new UnsignedLongDataType();
            }

        } else if (mainArg.startsWith("float")) {
            mainArg = mainArg.replaceFirst("float", "");
            argType = "float";
            typeToReturn = new FloatDataType();
        } else if (mainArg.startsWith("double")) {
            mainArg = mainArg.replaceFirst("double", "");
            argType = "double";
            typeToReturn = new DoubleDataType();
        } else if (mainArg.startsWith("long double")) {
            mainArg = mainArg.replaceFirst("long double", "");
            argType = "longdouble";
            isUnsigned = false;
            typeToReturn = new LongDoubleDataType();
        } else if (mainArg.startsWith("__int64")) {
            mainArg = mainArg.replaceFirst("__int64", "");
            argType = "INT64";
            typeToReturn = new LongLongDataType();
            if (isUnsigned == true) {
                argType = "U" + argType;
                typeToReturn = new UnsignedLongLongDataType();
            }

        } else if (mainArg.startsWith("bool")) {
            mainArg = mainArg.replaceFirst("bool", "");
            argType = "bool";
        } else {
            argType = "undefined4";
            isUnsigned = false;
        }


        String innerPointers = new String();

        if ((mainArg.equals(" *") || mainArg.equals(" * *")) && argType != "longdouble") {
            if (mainArg.equals(" * *")) {
                typeToReturn = new PointerDataType(new PointerDataType(typeToReturn));
                mainArg = "";
            } else {
                typeToReturn = new PointerDataType(typeToReturn);
            }
            innerPointers = mainArg;
            printDebug("Inner pointers: " + innerPointers);
        } else if (mainArg.equals("&")) {
            innerPointers = " *";
            typeToReturn = new PointerDataType(typeToReturn);
        }

        printDebug("Inner arg: " + mainArg);

        argType += innerPointers;

        return typeToReturn;
    }

    private String copyLastOp(String opCopy) {

        switch (opCopy) {

            case "add":
                return "+";

            case "adr":
                return "&";

            case "and":
                return "&";

            case "asg":
                return "=";

            case "land":
                return "&&";

            case "lor":
                return "||";

            case "call":
                return "()";

            case "cmp":
                return "~";

            case "fnc":
                return "()";

            case "dec":
                return "--";

            case "dele":
                return "delete";

            case "div":
                return "/";

            case "eql":
                return "==";

            case "geq":
                return ">=";

            case "gtr":
                return ">";

            case "inc":
                return "++";

            case "ind":
                return "*";

            case "leq":
                return "<=";

            case "lsh":
                return "<<";

            case "lss":
                return "<";

            case "mod":
                return "%";

            case "mul":
                return "*";

            case "neq":
                return "!=";

            case "new":
                return "new";

            case "not":
                return "!";

            case "or":
                return "|";

            case "rand":
                return "&=";

            case "rdiv":
                return "/=";

            case "rlsh":
                return "<<=";

            case "rmin":
                return "-=";

            case "rmod":
                return "%=";

            case "rmul":
                return "*=";

            case "ror":
                return "|=";

            case "rplu":
                return "+=";

            case "rrsh":
                return ">>=";

            case "rsh":
                return ">>";

            case "rxor":
                return "^=";

            case "subs":
                return "[]";

            case "sub":
                return "-";

            case "xor":
                return "^";

            case "arow":
                return "->";

            case "nwa":
                return "new[]";

            case "dla":
                return "delete[]";

        }

        return "";
    }

    private String copyUntil(char finishingCharacter) throws NameError {
        String returnString = new String();

        char charHold = thisChar();
        while (charHold != finishingCharacter && charPtr < funcName.length() && charHold != 0) {
            returnString += charHold;
            charHold = nextChar();
        }

        return returnString;
    }


    private String copyUntil2(char finishingCharacter, char finishingCharacter2) throws NameError {
        String returnString = new String();

        char charHold = thisChar();
        while (charHold != finishingCharacter && charHold != finishingCharacter2 && charPtr < funcName.length() && charHold != 0) {
            returnString += charHold;
            charHold = nextChar();
        }

        return returnString;
    }

    private boolean nameEnded() {
        if (charPtr >= funcName.length()-1) {
            return true;
        }
        return false;
    }

    private String copyArgsDelphi(char finishingCharacter, boolean templArgs) throws NameError {
        String returnString = new String();

        try {

            char charHold = thisChar();
            boolean first = true;
            char termChar = 0;

            while (charHold != finishingCharacter) {

                int charBegin = charPtr;

                if (first == true) {
                    first = false;
                } else {
                    returnString += ", ";
                }

                /* Skip the kind character */
                nextChar();


                switch (charHold) {
                    case 't':
                        returnString += copyType(!templArgs, false);
                        break;

                    case 'T':
                        returnString += "<type ";
                        termChar = '>';
                        /* Fallthrough */

                    case 'i':
                        if (funcName.charAt(charBegin) == '4' && funcName.substring(charBegin+1, charBegin+5) == "bool") {
                            if (thisChar() == '0') {
                                returnString += "false";
                            } else {
                                returnString += "true";
                            }
                            nextChar();
                            break;
                        }

                    case 'j':
                    case 'g':
                    case 'e':

                        /* Skip type */
                        copyType(!templArgs, false);

                        if (thisChar() != '$') {
                            throw new NameError("Symbol parsing failed: arglist expected at " + charPtr);
                        }

                        nextChar();

                        returnString += copyUntil2('$', '%');
                        if (termChar != 0) {
                            returnString += termChar;
                        }
                        break;

                    case 'm':

                        /* Skip type */
                        copyType(!templArgs, false);

                        if (thisChar() != '$') {
                            throw new NameError("Symbol parsing failed: arglist expected at " + charPtr);
                        }

                        nextChar();

                        returnString += copyUntil('$');

                        returnString += "::*";
                        returnString += copyUntil2('$', '%');
                        break;

                    default:
                        throw new NameError("Unknown template arg kind at " + charPtr);
                }

                charHold = thisChar();
                if (charHold != finishingCharacter) {
                    if (charHold != '$') {
                         throw new NameError("Symbol parsing failed: arglist expected at " + charPtr);
                    }
                    charHold = nextChar();
                }
            }
        } catch (NameError err) {
            onErrorReturn = returnString + onErrorReturn;
            throw err;
        }

        return returnString;
    }

    private int clauseCounter = 1;

    private String copyName(boolean templName, boolean isMaster, int untilChar) throws NameError {

        printDebug("Copy name called");

        String returnString = new String();

        String returnFlags = new String();

        boolean isDelphi = false;

        try {

            char charHold = thisChar();

            while (true) {

                if (Character.isDigit(charHold)) {

                    printDebug("Copy flags digit");

                    int flags = charHold - '0' + 1;

                    if ((flags & 1) > 0) {
                        vtblFlags.add(VTableFlag.HUGE);
                    }

                    if ((flags & 2) > 0) {
                        vtblFlags.add(VTableFlag.FASTTHIS);
                    }

                    if ((flags & 4) > 0) {
                        vtblFlags.add(VTableFlag.RTTI);
                    }

                    functionSymbolKind = SymbolKind.VTABLE;

                    charHold = nextChar();

                    if (charHold != 0 && charHold != '$') {
                        throw new NameError("Symbol parsing failed: arglist expected at " + charPtr);
                    }
                }

                printDebug("Switch was called");

                switch (charHold) {

                    /* Qualifier */
                    case '@':

                        charHold = nextChar();

                        if (charHold == '$') {

                            if (nextChar() != 'c') {
                                throw new NameError("Symbol parsing failed: wrong qualifier character sequence at " + charPtr);
                            }

                            if (nextChar() != 'f') {
                                throw new NameError("Symbol parsing failed: wrong qualifier character sequence at " + charPtr);
                            }

                            if (nextChar() != '$') {
                                throw new NameError("Symbol parsing failed: wrong qualifier character sequence at " + charPtr);
                            }

                            if (nextChar() != '@') {
                                throw new NameError("Symbol parsing failed: wrong qualifier character sequence at " + charPtr);
                            }

                            returnFlags = "__vdflg__ ";

                            if (isMaster == true) {
                                flagsList += returnFlags;
                            } else {
                                returnString += returnFlags;
                            }

                            nextChar();
                            String retStrName = copyName(false, false, -1);
                            returnString += retStrName;
                            functionModifier = Modifier.VIRDEF_FLAG;

                        } else {

                            returnFlags = "__linkproc__ ";
                            if (isMaster == true) {
                                flagsList += returnFlags;
                            } else {
                                returnString += returnFlags;
                            }


                            String retStrName = copyName(false, false, -1);
                            returnString += retStrName;

                            functionModifier = Modifier.LINKER_PROC;
                        }
                        printDebug("Qualifier found returned");
                        return returnString;

                    /* Tmplcode */
                    case '%':

                        printDebug("Tmplcode detected at " + charPtr);

                        charHold = nextChar();

                        if (charHold == 'S' || charHold == 'D') {
                            String restSubStr = funcName.substring(charPtr, funcName.length());
                            if (restSubStr.startsWith("Set$") || restSubStr.startsWith("DynamicArray$") || restSubStr.startsWith("SmallString$") || restSubStr.startsWith("DelphiInterface$")) {
                                isDelphi = true;
                                printDebug("Delphi argument detected!");
                            }
                        }

                        String retStrName = copyName(true, false, -1);
                        returnString += retStrName;

                        /* Arglist */
                        if (thisChar() != '$') {
                            throw new NameError("Symbol parsing failed: arglist expected at " + thisChar() + " " + charPtr);
                        }

                        nextChar();

                        if (returnString.charAt(returnString.length()-1) == '<') {
                            returnString += " ";
                        }

                        returnString += "<";

                        int counterCl = clauseCounter;
                        clauseCounter+= 1;

                        String argsStr = new String();
                        if (isDelphi == true) {
                            argsStr = copyArgsDelphi('%', true);
                        } else {
                            argsStr = copyArgs('%', true, false);
                        }
                        returnString += argsStr;

                        if (returnString.charAt(returnString.length()-1) == '>') {
                            returnString += " ";
                        }

                        returnString += ">";

                        if (thisChar() != '%') {
                            throw new NameError("Symbol parsing failed: tmplcode expected at " + charPtr);
                        }

                        nextChar();

                        if (thisChar() != '@') {
                            if (functionUniqModifiers.contains(ModifierUniq.TEMPLATE) == false) {
                                functionUniqModifiers.add(ModifierUniq.TEMPLATE);
                            }
                        }

                        break;

                    /* Arglist */
                    case '$':
                        printDebug("Arglist detected");

                        if (templName == true) {
                            return returnString;
                        }
                        charHold = nextChar();

                        if (charHold == 'x') {
                            charHold = nextChar();
                            if (charHold == 'p' || charHold == 't') {
                                if (nextChar() != '$') {
                                    throw new NameError("Symbol parsing failed: wrong arglist character sequence at " + charPtr);
                                }
                                nextChar();
                                returnFlags = "__tpdsc__ ";
                                if (isMaster == true) {
                                    flagsList += returnFlags;
                                } else {
                                    returnString += returnFlags;
                                }

                                returnString += copyType(false, false);
                                functionSymbolKind = SymbolKind.TPDSC;
                                return returnString;
                            } else {
                                throw new NameError("Symbol parsing failed: wrong arglist character sequence at " + charPtr);
                            }
                        }

                        if (charHold == 'b') {
                            charHold = nextChar();
                            int charPtrHold = charPtr;
                            if (charHold == 'c' || charHold == 'd') {
                                if (nextChar() == 't') {
                                    if (nextChar() == 'r') {
                                        if (nextChar() != '$') {
                                            throw new NameError("Symbol parsing failed: arglist expected at " + charPtr);
                                        }
                                        if (charHold == 'c') {
                                            functionSymbolKind = SymbolKind.CONSTRUCTOR;
                                        } else {
                                            functionSymbolKind = SymbolKind.DESTRUCTOR;
                                        }
                                        break;
                                    }
                                }
                            }

                            charPtr = charPtrHold;

                            returnString += "operator ";

                            returnString += copyLastOp(copyUntil('$'));

                            functionSymbolKind = SymbolKind.OPERATOR;

                        } else if (charHold == 'o') {
                            nextChar();

                            returnString += "operator ";

                            returnString += copyType(false, false);

                            if (thisChar() != '$') {
                                throw new NameError("Symbol parsing failed: arglist expected at " + charPtr);
                            }

                            functionSymbolKind = SymbolKind.CONVERSION;
                        } else if (charHold == 'v' || charHold == 'd') {
                            char tKind = charHold;
                            charHold = nextChar();

                            if (tKind == 'v' && charHold == 's') {
                                charHold = nextChar();
                                if (charHold != 'f' && charHold != 'n') {
                                    throw new NameError("Symbol parsing failed: wrong arglist character sequence at " + charPtr);
                                }
                                nextChar();

                                returnFlags = "__vdthk__";
                                if (isMaster == true) {
                                    flagsList += returnFlags;
                                } else {
                                    returnString += returnFlags;
                                }

                                functionSymbolKind = SymbolKind.VRDF_THUNK;

                            } else if (charHold == 'c') {
                                charHold = nextChar();
                                if (Character.isDigit(charHold) == false) {
                                    throw new NameError("Symbol parsing failed: wrong arglist character sequence at " + charPtr);
                                }
                                charHold = nextChar();
                                if (charHold != '$') {
                                    throw new NameError("Symbol parsing failed: wrong arglist character sequence at " + charPtr);
                                }
                                charHold = nextChar();

                                returnFlags = "__thunk__ [";

                                if (tKind == 'v') {
                                    functionSymbolKind = SymbolKind.THUNK;
                                } else {
                                    functionSymbolKind = SymbolKind.DYN_THUNK;
                                }

                                thunkArguments.add(""+charHold);
                                returnFlags += charHold + ",";

                                charHold = nextChar();

                                String newFlagArg1 = copyUntil('$');
                                thunkArguments.add(""+newFlagArg1);
                                returnFlags += newFlagArg1;

                                returnFlags += charHold + ",";

                                charHold = nextChar();

                                String newFlagArg2 = copyUntil('$');
                                thunkArguments.add(""+newFlagArg2);
                                returnFlags += newFlagArg2;

                                returnFlags += charHold + ",";

                                charHold = nextChar();

                                String newFlagArg3 = copyUntil('$');
                                thunkArguments.add(""+newFlagArg3);
                                returnFlags += newFlagArg3;

                                returnFlags += "]";

                                if (isMaster == true) {
                                    flagsList += returnFlags;
                                } else {
                                    returnString += returnFlags;
                                }

                                /* Skip last arglist */
                                nextChar();

                                return returnString;
                            }

                        } else {
                            throw new NameError("Symbol parsing failed: unknown special name at " + charPtr);
                        }

                        break;

                    case '_':

                        int charPtrCopied = charPtr;

                        if (nextChar() == '$') {
                            charHold = nextChar();

                            /*
                                In Borland there are five kinds of special names:

                                frndl | FL  | friend list
                                chtbl | CH  | catch handler table
                                odtbl | DC  | object destructor table
                                thrwl | TL  | throw list
                                ectbl | ECT | exception context table

                            */

                            returnFlags = "__";

                            switch ((funcName.charAt(charPtr)<<8)|funcName.charAt(charPtr+1)) {

                                /* Friend list */
                                case 0x464c:
                                    returnFlags += "frndl";
                                    functionModifier = Modifier.FRIEND_LIST;
                                    break;

                                /* Catcher handle table */
                                case 0x4348:
                                    returnFlags += "chtbl";
                                    functionModifier = Modifier.CTCH_HNDL_TBL;
                                    break;

                                /* Object destructor table */
                                case 0x4443:
                                    returnFlags += "odtbl";
                                    functionModifier = Modifier.OBJ_DEST_TBL;
                                    break;

                                /* Throw list */
                                case 0x544c:
                                    returnFlags += "thrwl";
                                    functionModifier = Modifier.THROW_LIST;
                                    break;

                                /* Exception context table */
                                case 0x4543:
                                    returnFlags += "ectbl";
                                    functionModifier = Modifier.EXC_CTXT_TBL;
                                    break;
                            }

                            returnFlags += "__ ";

                            if (isMaster == true) {
                                flagsList += returnFlags;
                            } else {
                                returnString += returnFlags;
                            }

                            while (charHold >= 'A' && charHold <= 'Z') {
                                charHold = nextChar();
                            }

                            if (charHold != '$') {
                                throw new NameError("Symbol parsing failed: arglist expected at " + charPtr);
                            }

                            if (nextChar() != '@') {
                                throw new NameError("Symbol parsing failed: qualifier expected at " + charPtr);
                            }

                            nextChar();

                            returnString += copyName(false, false, -1);

                            return returnString;

                        }

                        charPtr = charPtrCopied;

                        /* Fallthrough */

                    default:
                        printDebug("Run copy until");
                        returnString += copyUntil2('@', '$');

                        break;

                }

                charHold = thisChar();

                if (charHold != 0 && charHold != '@' && charHold != '$') {
                    throw new NameError("Symbol parsing failed: found wrong character sequence at " + charPtr);
                }

                if (charHold == '@') {

                    charHold = nextChar();

                    if (functionUniqModifiers.contains(ModifierUniq.QUALIFIED) == false) {
                        functionUniqModifiers.add(ModifierUniq.QUALIFIED);
                    }

                    returnString += "::";

                    if (charHold != 0) {

                        functionSymbolKind = SymbolKind.VTABLE;
                    }

                } else {
                    break;
                }
            }

            printDebug("End copy name");
        } catch (NameError err) {
            onErrorReturn = returnString + onErrorReturn;
            throw err;
        }

        return returnString;

    }

    private char nextChar() {
        charPtr += 1;

        if (charPtr > funcName.length()-1) {
            return 0;
        }

        printDebug("New char is: " + charPtr + " " + funcNameChars[charPtr]);

        return funcNameChars[charPtr];
    }

    private char thisChar() {
        if (charPtr > funcName.length()-1) {
            return 0;
        }
        return funcNameChars[charPtr];
    }

    private String copyType(boolean argLevel, boolean mainType) throws NameError {

        printDebug("Run copy type");

        String returnString = new String();

        try {

            String tName = new String();
            char charHold = thisChar();

            boolean typeUnsigned = false;
            boolean typeSigned = false;
            boolean typeConst = false;
            boolean typeVolatile = false;

            int loopLimit = 100;
            char saveChar = 0;

            boolean loopStop = false;

            /* Process type qualifiers */
            while (loopStop == false) {

                loopLimit -= 1;

                if (loopLimit == 0) {
                    throw new NameError("Symbol parsing failed: type copying loop out of range at " + charPtr);
                }

                switch (charHold) {
                    case 'u':
                        typeUnsigned = true;
                        break;
                    case 'z':
                        typeSigned = true;
                        break;
                    case 'x':
                        typeConst = true;
                        break;
                    case 'w':
                        typeVolatile = true;
                        break;
                    case 'y':
                        charHold = nextChar();
                        if (charHold != 'f' && charHold != 'n') {
                            throw new NameError("Symbol parsing failed: type closure syntax invalid at " + charPtr);
                        }
                        returnString += "__closure";
                        break;

                    default:
                        loopStop = true;
                        break;

                }

                if (loopStop == false) {
                    charHold = nextChar();
                }

            }

            /* Enum or class name */
            if (Character.isDigit(charHold) == true) {
                int i = 0;

                /* Determine length */

                String lenString = new String();

                do {
                    lenString += charHold;
                    charHold = nextChar();
                } while (Character.isDigit(charHold) == true);

                i = Integer.parseInt(lenString);

                int m = charPtr;

                for (int len = i; len > 0; m += 1) {

                    if (m > LENGTH_LIMIT || m > funcName.length()) {
                        throw new NameError("Unexpected name's end at " + m);
                    }

                    len -= 1;
                }

                if (typeConst == true) {
                    returnString += "const ";
                }

                if (typeVolatile == true) {
                    returnString += "volatile ";
                }

                char toSave = 0;

                int charToSkip = charPtr+i;

                if (charToSkip < funcName.length()) {

                    toSave = funcNameChars[charToSkip];

                    funcNameChars[charToSkip] = 0;

                }

                printDebug("New function name: " + funcName);

                String retStrName = copyName(false, false, charPtr+i);
                returnString += retStrName;

                if (charToSkip < funcName.length()) {

                    printDebug("Char zeroed: " + charToSkip + " Char current: " + charPtr);

                    funcNameChars[charPtr] = toSave;

                }



                printDebug("Return argument");

                return returnString;

            }

            saveChar = charHold;

            switch (charHold) {

                case 'v':
                    tName = "void";
                    break;

                case 'c':
                    tName = "char";
                    break;

                case 'b':
                    tName = "wchar_t";
                    break;

                case 's':
                    tName = "short";
                    break;

                case 'i':
                    tName = "int";
                    break;

                case 'l':
                    tName = "long";
                    break;

                case 'f':
                    tName = "float";
                    break;

                case 'd':
                    tName = "double";
                    break;

                case 'g':
                    tName = "long double";
                    break;

                case 'j':
                    tName = "__int64";
                    break;

                case 'o':
                    tName = "bool";
                    break;

                case 'e':
                    tName = "...";
                    break;

                /* Member pointer */
                case 'M':

                    nextChar();

                    outputString += copyType(false, false);


                /* Reference */
                case 'r':

                /* Pointer */
                case 'p':

                    charHold = nextChar();

                    /* Function pointer */
                    if (charHold == 'q') {

                        returnString += "(";

                        if (saveChar == 'M') {

                            if (outputString.isEmpty() == true) {
                                throw new NameError("Type pointer output is empty at " + charPtr);
                            }

                            returnString += outputString + "::";

                        }

                        returnString += "*)";

                        saveChar = charHold;
                    }

                    printDebug("Pointer type copy");

                    returnString += copyType(false, false);

                    if (saveChar == 'r') {
                        returnString += "&";
                    } else if (saveChar == 'p') {
                        returnString += " *";
                    } else if (saveChar == 'M') {
                        if (outputString.isEmpty()) {
                            throw new NameError("Symbol parsing failed: wrong pointer character sequence at " + charPtr);
                        }
                        returnString += " " + outputString + "::*";
                    }

                    break;

                /* Array */
                case 'a':
                    String dimStr = new String();

                    do {

                        charHold = nextChar();

                        dimStr += "[";

                        if (charHold == '0') {
                            charHold = nextChar();
                        }

                        dimStr += copyUntil('$');

                        if (charHold != '$') {
                            throw new NameError("Symbol parsing failed: arglist expected at " + charPtr);
                        }

                        charHold = nextChar();

                        dimStr += "]";

                    } while (charHold == 'a');

                    returnString += copyType(false, false);

                    returnString += dimStr;

                    break;

                /* Function */
                case 'q':

                    printDebug("Function intro detected");

                    boolean hasReturn = false;
                    boolean saveAdjQual = false;

                    while (true) {

                        if (nextChar() != 'q') {
                            break;
                        }

                        switch (nextChar()) {

                            case 'c':
                                callConvent = "__cdecl";
                                break;
                            case 'p':
                                callConvent = "__pascal";
                                break;
                            case 'r':
                                callConvent = "__fastcall";
                                break;
                            case 'f':
                                callConvent = "__fortran";
                                break;
                            case 's':
                                callConvent = "__stdcall";
                                break;
                            case 'y':
                                callConvent = "__syscall";
                                break;
                            case 'i':
                                callConvent = "__interrupt";
                                break;
                            case 'g':
                                regConvent = "__saveregs";
                                break;

                        }
                    }

                    returnString += "(";

                    printDebug("Run copy args");

                    if (mainType == true) {
                        returnString += copyArgs('$', false, true);
                    } else {
                        returnString += copyArgs('$', false, false);
                    }

                    returnString += ")";

                    if (thisChar() == '$') {
                        hasReturn = true;
                        nextChar();
                    }

                    if (hasReturn == true) {
                        returnType = copyType(false, false);
                        printDebug("Return type new is: " + returnType);
                    }

                    break;


                default:
                    throw new NameError("Unknown type at " + charPtr);

            }

            if (tName.isEmpty() == false) {

                if (typeConst == true) {
                    returnString += "const ";
                }

                if (typeVolatile == true) {
                    returnString += "volatile ";
                }

                if (typeSigned == true) {
                    returnString += "signed ";
                }

                if (typeUnsigned == true) {
                    returnString += "unsigned ";
                }

                if (argLevel == false || saveChar != 'v') {
                    returnString += tName;
                }

                nextChar();

            } else {
                if (typeConst == true) {
                    returnString += " const";
                }

                if (typeVolatile == true) {
                    returnString += " volatile";
                }

            }

            printDebug("Finish copy type");
        } catch (NameError err) {
            onErrorReturn = returnString + onErrorReturn;
            throw err;
        }

        return returnString;

    }

    private String copyArgs(char finishingCharacter, boolean templArgs, boolean mainArgs) throws NameError {

        String[] paramStrings = new String[TABLE_LIMIT];

        String returnString = new String();

        String argString = new String();


        printDebug("Copyargs initialized");

        try {

            char charHold = thisChar();

            boolean atStart = true;

            int paramIndex = 0;

            while (charHold != 0 && charHold != finishingCharacter) {
                argString = new String();
                printDebug("Copying arguments, from char: " + charPtr);

                if (atStart == true) {
                    atStart = false;
                } else {
                    returnString += ", ";
                }

                int savePtr = charPtr;

                boolean delphiScanned = false;

                while (charHold == 'x' || charHold == 'w') {
                    delphiScanned = true;
                    charHold = nextChar();
                }

                if (delphiScanned == true && charHold != 't') {
                    printDebug("Delphi scanned");
                    charPtr = savePtr;
                }

                if (charHold != 't') {
                    printDebug("Call copyType argument");
                    paramStrings[paramIndex] = copyType(!templArgs, false);
                    argString += paramStrings[paramIndex];
                } else {
                    int indxVal;

                    charHold = nextChar();

                    if (Character.isDigit(charHold)) {
                        indxVal = charHold - '0';
                    } else {
                        indxVal = (charHold - 'a') + 10;
                    }

                    indxVal -= 1;

                    if (paramStrings[indxVal] == null) {
                        throw new NameError("Symbol parsing failed: name not found at index " + indxVal);
                    }

                    argString += paramStrings[indxVal];

                    nextChar();
                }

                paramIndex += 1;

                charHold = thisChar();

                if (templArgs == true && charHold == '$') {
                    char termChar = 0;

                    charHold = nextChar();

                    nextChar();

                    switch (charHold) {
                        case 'T':
                            argString += "<type ";
                            termChar = '>';

                            /* Fallthrough */

                        case 'i':
                            if  (funcName.charAt(savePtr) == '4' && funcName.substring(savePtr+1, savePtr+5) == "bool") {

                                if (thisChar() == '0') {
                                    argString += "false";
                                } else {
                                    argString += "true";
                                }

                                nextChar();
                                break;
                            }

                            /* Fallthrough */

                        case 'j':
                        case 'g':
                        case 'e':
                            argString += copyUntil('$');
                            if  (termChar != 0) {
                                argString += termChar;
                            }
                            break;

                        case 'm':
                            argString += copyUntil('$');
                            argString += "::*";
                            argString += copyUntil('$');
                            break;

                        default:
                            throw new NameError("Unknown template argument kind at " + charPtr);
                    }

                    if (thisChar() != '$') {
                        throw new NameError("Symbol parsing failed: arglist expected at " + charPtr);
                    }

                    charHold = nextChar();

                }

                if (mainArgs == true && argString.isEmpty() == false) {
                    printDebug("Added args " + argString);
                    mainArgumentsList.add(argString);
                }

                returnString += argString;

            }

            if (charHold != finishingCharacter && prevTemplClose == true) {
                prevTemplClose = false;
            }

        } catch (NameError err) {
            onErrorReturn = returnString + onErrorReturn;
            throw err;
        }

        printDebug("End copy args");

        return returnString;
    }

}
