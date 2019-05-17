// Tank2 裁判程序
// 作者：289371298 upgraded from zhouhy
// https://www.botzone.org.cn/games/Tank2
// major changes in interfaces:
// field--->brickfield,waterfield & steelfield
// output["display"]=initdata["field"]--->output["display"]["brickfield"],["display"]["waterfield"],["display"]["steelfield"]
#include <stack>
#include <set>
#include <string>
#include <iostream>
#include <ctime>
#include <cstring>
#include <queue>
#ifdef _BOTZONE_ONLINE
#include "jsoncpp/json.h"
#else
#include <json/json.h>
#endif

using std::string;
using std::cin;
using std::cout;
using std::endl;
using std::getline;
using std::queue;
namespace TankGame
{
    using std::stack;
    using std::set;
    using std::istream;

#ifdef _MSC_VER
#pragma region 常量定义和说明
#endif

    enum GameResult
    {
        NotFinished = -2,
        Draw = -1,
        Blue = 0,
        Red = 1
    };

    enum FieldItem
    {
        None = 0,
        Brick = 1,
        Steel = 2,
        Base = 4,
        Blue0 = 8,
        Blue1 = 16,
        Red0 = 32,
        Red1 = 64,
        Water = 128
    };

    template<typename T> inline T operator~ (T a) { return (T)~(int)a; }
    template<typename T> inline T operator| (T a, T b) { return (T)((int)a | (int)b); }
    template<typename T> inline T operator& (T a, T b) { return (T)((int)a & (int)b); }
    template<typename T> inline T operator^ (T a, T b) { return (T)((int)a ^ (int)b); }
    template<typename T> inline T& operator|= (T& a, T b) { return (T&)((int&)a |= (int)b); }
    template<typename T> inline T& operator&= (T& a, T b) { return (T&)((int&)a &= (int)b); }
    template<typename T> inline T& operator^= (T& a, T b) { return (T&)((int&)a ^= (int)b); }

    enum Action
    {
        Invalid = -2,
        Stay = -1,
        Up, Right, Down, Left,
        UpShoot, RightShoot, DownShoot, LeftShoot
    };

    // 坐标左上角为原点（0, 0），x 轴向右延伸，y 轴向下延伸
    // Side（对战双方） - 0 为蓝，1 为红
    // Tank（每方的坦克） - 0 为 0 号坦克，1 为 1 号坦克
    // Turn（回合编号） - 从 1 开始

    const int fieldHeight = 9, fieldWidth = 9, sideCount = 2, tankPerSide = 2;

    // 基地的横坐标
    const int baseX[sideCount] = { fieldWidth / 2, fieldWidth / 2 };

    // 基地的纵坐标
    const int baseY[sideCount] = { 0, fieldHeight - 1 };

    const int dx[4] = { 0, 1, 0, -1 }, dy[4] = { -1, 0, 1, 0 };
    const FieldItem tankItemTypes[sideCount][tankPerSide] = {
        { Blue0, Blue1 },{ Red0, Red1 }
    };

    int maxTurn = 100;

#ifdef _MSC_VER
#pragma endregion

#pragma region 工具函数和类
#endif

    inline bool ActionIsMove(Action x)
    {
        return x >= Up && x <= Left;
    }

    inline bool ActionIsShoot(Action x)
    {
        return x >= UpShoot && x <= LeftShoot;
    }

    inline bool ActionDirectionIsOpposite(Action a, Action b)
    {
        return a >= Up && b >= Up && (a + 2) % 4 == b % 4;
    }

    inline bool CoordValid(int x, int y)
    {
        return x >= 0 && x < fieldWidth && y >= 0 && y < fieldHeight;
    }

    // 判断 item 是不是叠在一起的多个坦克
    inline bool HasMultipleTank(FieldItem item)
    {
        // 如果格子上只有一个物件，那么 item 的值是 2 的幂或 0
        // 对于数字 x，x & (x - 1) == 0 当且仅当 x 是 2 的幂或 0
        return !!(item & (item - 1));
    }

    inline int GetTankSide(FieldItem item)
    {
        return item == Blue0 || item == Blue1 ? Blue : Red;
    }

    inline int GetTankID(FieldItem item)
    {
        return item == Blue0 || item == Red0 ? 0 : 1;
    }

    // 获得动作的方向
    inline int ExtractDirectionFromAction(Action x)
    {
        if (x >= Up)
            return x % 4;
        return -1;
    }

    // 物件消失的记录，用于回退
    struct DisappearLog
    {
        FieldItem item;

        // 导致其消失的回合的编号
        int turn;

        int x, y;
        bool operator< (const DisappearLog& b) const
        {
            if (x == b.x)
            {
                if (y == b.y)
                    return item < b.item;
                return y < b.y;
            }
            return x < b.x;
        }
    };

#ifdef _MSC_VER
#pragma endregion

#pragma region TankField 主要逻辑类
#endif

    class TankField
    {
    public:
        //!//!//!// 以下变量设计为只读，不推荐进行修改 //!//!//!//

        // 游戏场地上的物件（一个格子上可能有多个坦克）
        FieldItem gameField[fieldHeight][fieldWidth] = {};

        // 坦克是否存活
        bool tankAlive[sideCount][tankPerSide] = { { true, true },{ true, true } };

        // 基地是否存活
        bool baseAlive[sideCount] = { true, true };

        // 坦克横坐标，-1表示坦克已炸
        int tankX[sideCount][tankPerSide] = {
            { fieldWidth / 2 - 2, fieldWidth / 2 + 2 },{ fieldWidth / 2 + 2, fieldWidth / 2 - 2 }
        };

        // 坦克纵坐标，-1表示坦克已炸
        int tankY[sideCount][tankPerSide] = { { 0, 0 },{ fieldHeight - 1, fieldHeight - 1 } };

        // 当前回合编号
        int currentTurn = 1;

        // 我是哪一方
        int mySide;

        // 用于回退的log
        stack<DisappearLog> logs;

        // 过往动作（previousActions[x] 表示所有人在第 x 回合的动作，第 0 回合的动作没有意义）
        Action previousActions[101][sideCount][tankPerSide] = { { { Stay, Stay },{ Stay, Stay } } };

        //!//!//!// 以上变量设计为只读，不推荐进行修改 //!//!//!//

        // 本回合双方即将执行的动作，需要手动填入
        Action nextAction[sideCount][tankPerSide] = { { Invalid, Invalid },{ Invalid, Invalid } };

        // 判断行为是否合法（出界或移动到非空格子算作非法）
        // 未考虑坦克是否存活
        bool ActionIsValid(int side, int tank, Action act)
        {
            if (act == Invalid)
                return false;
            if (act > Left && previousActions[currentTurn - 1][side][tank] > Left) // 连续两回合射击
                return false;
            if (act == Stay || act > Left)
                return true;
            int x = tankX[side][tank] + dx[act],
                y = tankY[side][tank] + dy[act];
            return CoordValid(x, y) && gameField[y][x] == None;// water cannot be stepped on
        }

        // 判断 nextAction 中的所有行为是否都合法
        // 忽略掉未存活的坦克
        bool ActionIsValid()
        {
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    if (tankAlive[side][tank] && !ActionIsValid(side, tank, nextAction[side][tank]))
                        return false;
            return true;
        }

    private:
        void _destroyTank(int side, int tank)
        {
            tankAlive[side][tank] = false;
            tankX[side][tank] = tankY[side][tank] = -1;
        }

        void _revertTank(int side, int tank, DisappearLog& log)
        {
            int &currX = tankX[side][tank], &currY = tankY[side][tank];
            if (tankAlive[side][tank])
                gameField[currY][currX] &= ~tankItemTypes[side][tank];
            else
                tankAlive[side][tank] = true;
            currX = log.x;
            currY = log.y;
            gameField[currY][currX] |= tankItemTypes[side][tank];
        }
    public:

        // 执行 nextAction 中指定的行为并进入下一回合，返回行为是否合法
        bool DoAction()
        {
            if (!ActionIsValid())
                return false;

            // 1 移动
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                {
                    Action act = nextAction[side][tank];

                    // 保存动作
                    previousActions[currentTurn][side][tank] = act;
                    if (tankAlive[side][tank] && ActionIsMove(act))
                    {
                        int &x = tankX[side][tank], &y = tankY[side][tank];
                        FieldItem &items = gameField[y][x];

                        // 记录 Log
                        DisappearLog log;
                        log.x = x;
                        log.y = y;
                        log.item = tankItemTypes[side][tank];
                        log.turn = currentTurn;
                        logs.push(log);

                        // 变更坐标
                        x += dx[act];
                        y += dy[act];

                        // 更换标记（注意格子可能有多个坦克）
                        gameField[y][x] |= log.item;
                        items &= ~log.item;
                    }
                }

            // 2 射♂击!
            set<DisappearLog> itemsToBeDestroyed;
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                {
                    Action act = nextAction[side][tank];
                    if (tankAlive[side][tank] && ActionIsShoot(act))
                    {
                        int dir = ExtractDirectionFromAction(act);
                        int x = tankX[side][tank], y = tankY[side][tank];
                        bool hasMultipleTankWithMe = HasMultipleTank(gameField[y][x]);
                        while (true)
                        {
                            x += dx[dir];
                            y += dy[dir];
                            if (!CoordValid(x, y))
                                break;
                            FieldItem items = gameField[y][x];
                            //tank will not be on water, and water will not be shot, so it can be handled as None
                            if (items != None && items != Water)
                            {
                                // 对射判断
                                if (items >= Blue0 &&
                                    !hasMultipleTankWithMe && !HasMultipleTank(items))
                                {
                                    // 自己这里和射到的目标格子都只有一个坦克
                                    Action theirAction = nextAction[GetTankSide(items)][GetTankID(items)];
                                    if (ActionIsShoot(theirAction) &&
                                        ActionDirectionIsOpposite(act, theirAction))
                                    {
                                        // 而且我方和对方的射击方向是反的
                                        // 那么就忽视这次射击
                                        break;
                                    }
                                }

                                // 标记这些物件要被摧毁了（防止重复摧毁）
                                for (int mask = 1; mask <= Red1; mask <<= 1)
                                    if (items & mask)
                                    {
                                        DisappearLog log;
                                        log.x = x;
                                        log.y = y;
                                        log.item = (FieldItem)mask;
                                        log.turn = currentTurn;
                                        itemsToBeDestroyed.insert(log);
                                    }
                                break;
                            }
                        }
                    }
                }

            for (auto& log : itemsToBeDestroyed)
            {
                switch (log.item)
                {
                case Base:
                {
                    int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
                    baseAlive[side] = false;
                    break;
                }
                case Blue0:
                    _destroyTank(Blue, 0);
                    break;
                case Blue1:
                    _destroyTank(Blue, 1);
                    break;
                case Red0:
                    _destroyTank(Red, 0);
                    break;
                case Red1:
                    _destroyTank(Red, 1);
                    break;
                case Steel:
                    continue;
                default:
                    ;
                }
                gameField[log.y][log.x] &= ~log.item;
                logs.push(log);
            }

            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    nextAction[side][tank] = Invalid;

            currentTurn++;
            return true;
        }

        // 回到上一回合
        bool Revert()
        {
            if (currentTurn == 1)
                return false;

            currentTurn--;
            while (!logs.empty())
            {
                DisappearLog& log = logs.top();
                if (log.turn == currentTurn)
                {
                    logs.pop();
                    switch (log.item)
                    {
                    case Base:
                    {
                        int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
                        baseAlive[side] = true;
                        gameField[log.y][log.x] = Base;
                        break;
                    }
                    case Brick:
                        gameField[log.y][log.x] = Brick;
                        break;
                    case Blue0:
                        _revertTank(Blue, 0, log);
                        break;
                    case Blue1:
                        _revertTank(Blue, 1, log);
                        break;
                    case Red0:
                        _revertTank(Red, 0, log);
                        break;
                    case Red1:
                        _revertTank(Red, 1, log);
                        break;
                    default:
                        ;
                    }
                }
                else
                    break;
            }
            return true;
        }

        // 游戏是否结束？谁赢了？
        GameResult GetGameResult()
        {
            bool fail[sideCount] = {};
            for (int side = 0; side < sideCount; side++)
                if ((!tankAlive[side][0] && !tankAlive[side][1]) || !baseAlive[side])
                    fail[side] = true;
            if (fail[0] == fail[1])
                return fail[0] || currentTurn > maxTurn ? Draw : NotFinished;
            if (fail[Blue])
                return Red;
            return Blue;
        }

        /* 三个 int 表示场地 01 矩阵（每个 int 用 27 位表示 3 行）
           initialize gameField[][]
           brick>water>steel
        */
        TankField(int hasBrick[3],int hasWater[3],int hasSteel[3], int mySide) : mySide(mySide)
        {
            for (int i = 0; i < 3; i++)
            {
                int mask = 1;
                for (int y = i * 3; y < (i + 1) * 3; y++)
                {
                    for (int x = 0; x < fieldWidth; x++)
                    {
                        if (hasBrick[i] & mask)
                            gameField[y][x] = Brick;
                        else if(hasWater[i] & mask)
                            gameField[y][x] = Water;
                        else if(hasSteel[i] & mask)
                            gameField[y][x] = Steel;
                        mask <<= 1;
                    }
                }
            }
            for (int side = 0; side < sideCount; side++)
            {
                for (int tank = 0; tank < tankPerSide; tank++)
                    gameField[tankY[side][tank]][tankX[side][tank]] = tankItemTypes[side][tank];
                gameField[baseY[side]][baseX[side]] = Base;
            }
        }

        // 打印场地
        void DebugPrint()
        {
#ifndef _BOTZONE_ONLINE
            const string side2String[] = { "蓝", "红" };
            const string boolean2String[] = { "已炸", "存活" };
            const char* boldHR = "==============================";
            const char* slimHR = "------------------------------";
            cout << boldHR << endl
                << "图例：" << endl
                << ". - 空\t# - 砖\t% - 钢\t* - 基地\t@ - 多个坦克" << endl
                << "b - 蓝0\tB - 蓝1\tr - 红0\tR - 红1\tW - 水" << endl //Tank2 feature
                << slimHR << endl;
            for (int y = 0; y < fieldHeight; y++)
            {
                for (int x = 0; x < fieldWidth; x++)
                {
                    switch (gameField[y][x])
                    {
                    case None:
                        cout << '.';
                        break;
                    case Brick:
                        cout << '#';
                        break;
                    case Steel:
                        cout << '%';
                        break;
                    case Base:
                        cout << '*';
                        break;
                    case Blue0:
                        cout << 'b';
                        break;
                    case Blue1:
                        cout << 'B';
                        break;
                    case Red0:
                        cout << 'r';
                        break;
                    case Red1:
                        cout << 'R';
                        break;
                    case Water:
                        cout << 'W';
                        break;
                    default:
                        cout << '@';
                        break;
                    }
                }
                cout << endl;
            }
            cout << slimHR << endl;
            for (int side = 0; side < sideCount; side++)
            {
                cout << side2String[side] << "：基地" << boolean2String[baseAlive[side]];
                for (int tank = 0; tank < tankPerSide; tank++)
                    cout << ", 坦克" << tank << boolean2String[tankAlive[side][tank]];
                cout << endl;
            }
            cout << "当前回合：" << currentTurn << "，";
            GameResult result = GetGameResult();
            if (result == -2)
                cout << "游戏尚未结束" << endl;
            else if (result == -1)
                cout << "游戏平局" << endl;
            else
                cout << side2String[result] << "方胜利" << endl;
            cout << boldHR << endl;
#endif
        }

        bool operator!= (const TankField& b) const
        {

            for (int y = 0; y < fieldHeight; y++)
                for (int x = 0; x < fieldWidth; x++)
                    if (gameField[y][x] != b.gameField[y][x])
                        return true;

            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                {
                    if (tankX[side][tank] != b.tankX[side][tank])
                        return true;
                    if (tankY[side][tank] != b.tankY[side][tank])
                        return true;
                    if (tankAlive[side][tank] != b.tankAlive[side][tank])
                        return true;
                }

            if (baseAlive[0] != b.baseAlive[0] ||
                baseAlive[1] != b.baseAlive[1])
                return true;

            if (currentTurn != b.currentTurn)
                return true;

            return false;
        }
    };

#ifdef _MSC_VER
#pragma endregion
#endif

    TankField *field;

#ifdef _MSC_VER
#pragma region 与平台交互部分
#endif

    // 内部函数
    namespace Internals
    {
        Json::Reader reader;
#ifdef _BOTZONE_ONLINE
        Json::FastWriter writer;
#else
        Json::StyledWriter writer;
#endif

        void _processRequestOrResponse(Json::Value& value, bool isOpponent)
        {
            if (value.isArray())
            {
                if (!isOpponent)
                {
                    for (int tank = 0; tank < tankPerSide; tank++)
                        field->nextAction[field->mySide][tank] = (Action)value[tank].asInt();
                }
                else
                {
                    for (int tank = 0; tank < tankPerSide; tank++)
                        field->nextAction[1 - field->mySide][tank] = (Action)value[tank].asInt();
                    field->DoAction();
                }
            }
            else
            {
                // 是第一回合，裁判在介绍场地
                int hasBrick[3],hasWater[3],hasSteel[3];
                for (int i = 0; i < 3; i++){//Tank2 feature(???????????????)
                    hasWater[i] = value["waterfield"][i].asInt();
                    hasBrick[i] = value["brickfield"][i].asInt();
                    hasSteel[i] = value["steelfield"][i].asInt();
                }
                field = new TankField(hasBrick,hasWater,hasSteel,value["mySide"].asInt());
            }
        }

        // 请使用 SubmitAndExit 或者 SubmitAndDontExit
        void _submitAction(Action tank0, Action tank1, string debug = "", string data = "", string globaldata = "")
        {
            Json::Value output(Json::objectValue), response(Json::arrayValue);
            response[0U] = tank0;
            response[1U] = tank1;
            output["response"] = response;
            if (!debug.empty())
                output["debug"] = debug;
            if (!data.empty())
                output["data"] = data;
            if (!globaldata.empty())
                output["globaldata"] = globaldata;
            cout << writer.write(output) << endl;
        }
    }

    // 从输入流（例如 cin 或者 fstream）读取回合信息，存入 TankField，并提取上回合存储的 data 和 globaldata
    // 本地调试的时候支持多行，但是最后一行需要以没有缩进的一个"}"或"]"结尾
    void ReadInput(istream& in, string& outData, string& outGlobalData)
    {
        Json::Value input;
        string inputString;
        do
        {
            getline(in, inputString);
        } while (inputString.empty());
#ifndef _BOTZONE_ONLINE
        // 猜测是单行还是多行
        char lastChar = inputString[inputString.size() - 1];
        if (lastChar != '}' && lastChar != ']')
        {
            // 第一行不以}或]结尾，猜测是多行
            string newString;
            do
            {
                getline(in, newString);
                inputString += newString;
            } while (newString != "}" && newString != "]");
        }
#endif
        Internals::reader.parse(inputString, input);

        if (input.isObject())
        {
            Json::Value requests = input["requests"], responses = input["responses"];
            if (!requests.isNull() && requests.isArray())
            {
                size_t i, n = requests.size();
                for (i = 0; i < n; i++)
                {
                    Internals::_processRequestOrResponse(requests[i], true);
                    if (i < n - 1)
                        Internals::_processRequestOrResponse(responses[i], false);
                }
                outData = input["data"].asString();
                outGlobalData = input["globaldata"].asString();
                return;
            }
        }
        Internals::_processRequestOrResponse(input, true);
    }

    // 提交决策并退出，下回合时会重新运行程序
    void SubmitAndExit(Action tank0, Action tank1, string debug = "", string data = "", string globaldata = "")
    {
        Internals::_submitAction(tank0, tank1, debug, data, globaldata);
        exit(0);
    }

    // 提交决策，下回合时程序继续运行（需要在 Botzone 上提交 Bot 时选择“允许长时运行”）
    // 如果游戏结束，程序会被系统杀死
    void SubmitAndDontExit(Action tank0, Action tank1)
    {
        Internals::_submitAction(tank0, tank1);
        field->nextAction[field->mySide][0] = tank0;
        field->nextAction[field->mySide][1] = tank1;
        cout << ">>>BOTZONE_REQUEST_KEEP_RUNNING<<<" << endl;
    }
#ifdef _MSC_VER
#pragma endregion
#endif
}

namespace TankJudge
{
    using namespace TankGame;

    int RandBetween(int from, int to)
    {
        return rand() % (to - from) + from;
    }

    int fieldBinary[3],waterBinary[3],steelBinary[3];

    bool visited[fieldHeight][fieldWidth];

    /*****************copied from TankField****************/
    int tankX[sideCount][tankPerSide] = {
        { fieldWidth / 2 - 2, fieldWidth / 2 + 2 },{ fieldWidth / 2 + 2, fieldWidth / 2 - 2 }
    };
    int tankY[sideCount][tankPerSide] = { { 0, 0 },{ fieldHeight - 1, fieldHeight - 1 } };
    /*****************************************************/

    int dirEnumerateList[][4] = {
        { Up, Right, Down, Left },
        { Up, Right, Left, Down },
        { Up, Down, Right, Left },
        { Up, Down, Left, Right },
        { Up, Left, Right, Down },
        { Up, Left, Down, Right },
        { Right, Up, Down, Left },
        { Right, Up, Left, Down },
        { Right, Down, Up, Left },
        { Right, Down, Left, Up },
        { Right, Left, Up, Down },
        { Right, Left, Down, Up },
        { Down, Up, Right, Left },
        { Down, Up, Left, Right },
        { Down, Right, Up, Left },
        { Down, Right, Left, Up },
        { Down, Left, Up, Right },
        { Down, Left, Right, Up },
        { Left, Up, Right, Down },
        { Left, Up, Down, Right },
        { Left, Right, Up, Down },
        { Left, Right, Down, Up },
        { Left, Down, Up, Right },
        { Left, Down, Right, Up }
    };
    //BFS to ensure that there is only one connected component
    //InitializeField already ensures that water&steel will not appear on base and tank
    struct node{int x,y;node(){}node(int xx,int yy){x=xx,y=yy;}};
    std::queue<node> q;
    bool EnsureConnected(bool hasWater[fieldHeight][fieldWidth],bool hasSteel[fieldHeight][fieldWidth]){
        int jishu = 0, jishu2 = 0;
        bool vis[fieldHeight][fieldWidth] = {0};
        for(int i = 0;i < fieldHeight; i++)
            for(int j = 0;j < fieldWidth; j++)
                if(!(hasWater[i][j]||hasSteel[i][j]))
                    jishu++;
        q.push(node(baseX[0],baseY[0]));
        vis[baseX[0]][baseY[0]] = 1;
        jishu2 = 1;
        while(!q.empty()){
            int x = q.front().x,y = q.front().y;
            q.pop();
            for(int i = 0;i < 4; i++){
                int eks = x + dx[i];
                int wai = y + dy[i];
                if(CoordValid(eks,wai) && !vis[eks][wai] && (!(hasWater[eks][wai]||hasSteel[eks][wai])) ){
                    q.push(node(eks,wai));
                    vis[eks][wai] = 1;
                    jishu2++;
                }
            }
        }
        return jishu2==jishu;
    }
    //initialize the battlefield before 1st round
    //insert water here
    void InitializeField()
    {
        memset(visited, 0, sizeof(visited));
        bool hasBrick[fieldHeight][fieldWidth] = {};
        bool hasWater[fieldHeight][fieldWidth] = {};
        bool hasSteel[fieldHeight][fieldWidth] = {};
        int portionH = (fieldHeight + 1) / 2;
        do{//optimistic approach: assume that disconnectivity will not appear normally
            for (int y = 0; y < portionH; y++)
                for (int x = 0; x < fieldWidth; x++){
                    hasBrick[y][x] = rand() % 3 > 1;// 1/3 brick
                    if(hasBrick[y][x]==false)hasWater[y][x] = rand() % 27 > 22; // (3/4)*(4/27)= 1/9 water
                    if(hasBrick[y][x]==false&&hasWater[y][x]==false)hasSteel[y][x]=rand() % 23 > 18;//(3/4)*(23/27)*(4/23)=1/9 steel
                }
            int bx = baseX[0], by = baseY[0];
            hasBrick[by + 1][bx + 1] = hasBrick[by + 1][bx - 1] =
                hasBrick[by][bx + 1] = hasBrick[by][bx - 1] = true;
            hasWater[by + 1][bx + 1] = hasWater[by + 1][bx - 1] =
                hasWater[by][bx + 1] = hasWater[by][bx - 1] = false;
            hasSteel[by + 1][bx + 1] = hasSteel[by + 1][bx - 1] =
                hasSteel[by][bx + 1] = hasSteel[by][bx - 1] = false;
            hasBrick[by + 1][bx] = true;
            hasBrick[by][bx] = hasBrick[by][bx + 2] = hasBrick[by][bx - 2] = false;
            hasWater[by][bx] = hasWater[by + 1][bx] = hasWater[by][bx + 2] = hasWater[by][bx - 2] = false;
            hasSteel[by][bx] = hasSteel[by + 1][bx] = hasSteel[by][bx + 2] = hasSteel[by][bx - 2] = false;
            //symmetry
            for (int y = 0; y < portionH; y++)
                for (int x = 0; x < fieldWidth; x++){
                    hasBrick[fieldHeight - y - 1][fieldWidth - x - 1] = hasBrick[y][x];
                    hasWater[fieldHeight - y - 1][fieldWidth - x - 1] = hasWater[y][x];
                    hasSteel[fieldHeight - y - 1][fieldWidth - x - 1] = hasSteel[y][x];
                }
            //separate the field into 4 pieces, each with a tank
            for (int y = 2; y < fieldHeight - 2; y++){
                hasBrick[y][fieldWidth / 2] = true;
                hasWater[y][fieldWidth / 2] = false;
                hasSteel[y][fieldWidth / 2] = false;
            }
            for (int x = 0; x < fieldWidth; x++){
                hasBrick[fieldHeight / 2][x] = true;
                hasWater[fieldHeight / 2][x] = false;
                hasSteel[fieldHeight / 2][x] = false;
            }
            for (int side = 0; side < sideCount; side++)
            {
                for (int tank = 0; tank < tankPerSide; tank++)
                    hasSteel[tankY[side][tank]][tankX[side][tank]] = hasWater[tankY[side][tank]][tankX[side][tank]] = false;
                hasSteel[baseY[side]][baseX[side]] = hasWater[baseY[side]][baseX[side]] = hasBrick[baseY[side]][baseX[side]] = false;
            }
            //add steel onto midpoint&midtankpoint
            hasBrick[fieldHeight/2][fieldWidth/2]=false;
            hasWater[fieldHeight/2][fieldWidth/2]=false;
            hasSteel[fieldHeight/2][fieldWidth/2]=true;

            for (int tank = 0; tank < tankPerSide; tank++){
            hasSteel[fieldHeight/2][tankX[0][tank]]=true;
            hasWater[fieldHeight/2][tankX[0][tank]]=hasBrick[fieldHeight/2][tankX[0][tank]]=false;
            }
        }
        while(!EnsureConnected(hasWater,hasSteel));
        for (int i = 0; i < 3; i++)//3 row as one number
        {
            int mask = 1;
            for (int y = i * 3; y < (i + 1) * 3; y++)
            {
                for (int x = 0; x < fieldWidth; x++)
                {
                    if (hasBrick[y][x])
                        fieldBinary[i] |= mask;
                    else if(hasWater[y][x])
                        waterBinary[i] |= mask;
                    else if(hasSteel[y][x])
                        steelBinary[i] |= mask;
                    mask <<= 1;
                }
            }
        }
    }
}

void validateImpl()
{
    srand(time(0));
    int i = 0;
    while (true)
    {
        cout << i++ << endl;
        if (TankGame::field)
            delete TankGame::field;
        std::stack<TankGame::TankField> history;
        TankJudge::InitializeField();
        TankGame::field = new TankGame::TankField(TankJudge::fieldBinary,TankJudge::waterBinary,TankJudge::steelBinary,0);
        while (TankGame::field->GetGameResult() == -2)
        {
            for (int side = 0; side < TankGame::sideCount; side++)
                for (int tank = 0; tank < TankGame::tankPerSide; tank++)
                    while (true)
                    {
                        auto act = (TankGame::Action)TankJudge::RandBetween(TankGame::Stay, TankGame::LeftShoot + 1);
                        if (TankGame::field->ActionIsValid(side, tank, act))
                        {
                            TankGame::field->nextAction[side][tank] = act;
                            break;
                        }
                    }
            history.push(*TankGame::field);
            TankGame::field->DoAction();
        }
        while (!history.empty())
        {
            auto& f = history.top();
            auto bak = *TankGame::field;
            TankGame::field->Revert();
            if (f != *TankGame::field)
            {
                f.DoAction();
                cout << "error";
            }
            history.pop();
        }
    }
}

int main()
{
    unsigned int seed;
    const string int2str[] = { "0", "1" };

    Json::Reader reader;
    Json::Value input, temp, output;
    #ifdef _BOTZONE_ONLINE
    reader.parse(cin, input);
    #else
    char *s="{\"log\":[{\"keep_running\":false,\"memory\":160,\"output\":{\"command\":\"request\",\"content\":{\"0\":{\"brickfield\":[71620266,4718352,44783889],\"waterfield\":[0,0,0],\"steelfield\":[0,0,0],\"mySide\":0},\"1\":{\"brickfield\":[71620266,4718352,44783889],\"waterfield\":[0,0,0],\"steelfield\":[0,0,0],\"mySide\":1}},\"display\":[71620266,4718352,44783889]},\"time\":3,\"verdict\":\"OK\"},{\"0\":{\"keep_running\":true,\"memory\":165,\"time\":89,\"verdict\":\"OK\",\"debug\":\"DEBUG!\",\"response\":[6,7]},\"1\":{\"keep_running\":true,\"memory\":20,\"time\":4,\"verdict\":\"OK\",\"response\":[0,4]}},{\"keep_running\":false,\"memory\":15,\"output\":{\"command\":\"request\",\"content\":{\"0\":[0,4],\"1\":[6,7]},\"display\":{\"0\":[6,7],\"1\":[0,4]}},\"time\":3,\"verdict\":\"OK\"},{\"0\":{\"keep_running\":true,\"memory\":165,\"time\":1,\"verdict\":\"OK\",\"debug\":\"DEBUG!\",\"response\":[2,-1]},\"1\":{\"keep_running\":true,\"memory\":20,\"time\":0,\"verdict\":\"OK\",\"response\":[0,0]}},{\"keep_running\":false,\"memory\":15,\"output\":{\"command\":\"request\",\"content\":{\"0\":[0,0],\"1\":[2,-1]},\"display\":{\"0\":[2,-1],\"1\":[0,0]}},\"time\":2,\"verdict\":\"OK\"},{\"0\":{\"keep_running\":true,\"memory\":165,\"time\":0,\"verdict\":\"OK\",\"debug\":\"DEBUG!\",\"response\":[0,7]},\"1\":{\"keep_running\":true,\"memory\":20,\"time\":0,\"verdict\":\"OK\",\"response\":[7,0]}}],\"initdata\":{\"brickfield\":[71620266,4718352,44783889],\"waterfield\":[0,0,0],\"steelfield\":[0,0,0],\"maxTurn\":100,\"seed\":1552650152}}";
    reader.parse(s,input);

    //test
    {Json::FastWriter writer;
     printf("%s\n\n",s);
    cout << writer.write(input);}
    #endif
    Json::Value initdata = input["initdata"];

    if (initdata.isString())
        reader.parse(initdata.asString(), initdata);
    if (initdata.isString())
        initdata = Json::Value(Json::objectValue);

    temp = initdata["maxTurn"];
    if (temp.isInt())
        TankGame::maxTurn = temp.asUInt();
    initdata["maxTurn"] = TankGame::maxTurn;

    temp = initdata["seed"];
    if (temp.isInt())
        srand(seed = temp.asUInt());
    else
        srand(seed = time(nullptr));
    initdata["seed"] = seed;

    temp = initdata["brickfield"];
    if (temp.isArray() && !temp.isNull()){
        for (int i = 0; i < 3; i++)
            TankJudge::fieldBinary[i] = temp[i].asInt();
        initdata["brickfield"] = temp;
        temp = initdata["waterfield"];
        for (int i = 0; i < 3; i++)
            TankJudge::waterBinary[i] = temp[i].asInt();
        initdata["waterfield"] = temp;
        temp = initdata["steelfield"];
        for (int i = 0; i < 3; i++)
            TankJudge::steelBinary[i] = temp[i].asInt();
        initdata["steelfield"] = temp;
    }
    else
    {
        TankJudge::InitializeField();
        temp = Json::Value(Json::arrayValue);
        for (int i = 0; i < 3; i++)
            temp[i] = TankJudge::fieldBinary[i];
        initdata["brickfield"] = temp;
        temp = Json::Value(Json::arrayValue);
        for (int i = 0; i < 3; i++)
            temp[i] = TankJudge::waterBinary[i];
        initdata["waterfield"] = temp;
        temp = Json::Value(Json::arrayValue);
        for (int i = 0; i < 3; i++)
            temp[i] = TankJudge::steelBinary[i];
        initdata["steelfield"] = temp;
    }


    TankGame::field = new TankGame::TankField(TankJudge::fieldBinary,TankJudge::waterBinary,TankJudge::steelBinary, 0);

    input = input["log"];

    int size = input.size();
    if (size == 0)//before 1st round
    {
        for (int side = 0; side < TankGame::sideCount; side++)
        {
            auto obj = Json::Value(Json::objectValue);
            obj["brickfield"] = initdata["brickfield"];
            obj["waterfield"]=initdata["waterfield"];
            obj["steelfield"]=initdata["steelfield"];
            obj["mySide"] = side;
            output["content"][int2str[side]] = obj;
        }

        output["initdata"] = initdata;
        output["command"] = "request";
        //display has brick,water and steel
        output["display"]["brick"] = initdata["brickfield"];
        output["display"]["water"] = initdata["waterfield"];
        output["display"]["steel"] = initdata["steelfield"];
    }
    else
    {
        bool invalid[TankGame::sideCount] = {};
        //winning side {0,1}
        auto setWinner = [&] (int to) {
            if (to == -1)
                output["content"]["0"] = output["content"]["1"] = 1;
            else if (to == 1)
            {
                output["content"]["0"] = 0;
                output["content"]["1"] = 2;
            }
            else
            {
                output["content"]["0"] = 2;
                output["content"]["1"] = 0;
            }
        };
        for (int i = 1; i < size; i += 2)
        {
            bool isLast = size - 1 == i;
            Json::Value response = input[i];
            for (int side = 0; side < TankGame::sideCount; side++)//simulate each round
            {
                Json::Value raw = response[int2str[side]],
                    answer = raw["response"].isNull() ? raw["content"] : raw["response"];
                TankGame::Action act0, act1;
                if (answer.isArray() && answer[0U].isInt() && answer[1U].isInt())
                {
                    act0 = (TankGame::Action)answer[0U].asInt();
                    act1 = (TankGame::Action)answer[1U].asInt();
                    if (isLast)
                    {
                        auto action = Json::Value(Json::arrayValue);
                        action[0U] = act0;
                        action[1U] = act1;
                        output["display"][int2str[side]] = output["content"][int2str[1 - side]] = action;
                        if (!TankGame::field->tankAlive[side][0] || !TankGame::field->ActionIsValid(side, 0, act0))
                            output["content"][int2str[1 - side]][0U] = -1;
                        if (!TankGame::field->tankAlive[side][1] || !TankGame::field->ActionIsValid(side, 1, act1))
                            output["content"][int2str[1 - side]][1U] = -1;
                    }
                    if ((!TankGame::field->tankAlive[side][0] || TankGame::field->ActionIsValid(side, 0, act0)) &&
                        (!TankGame::field->tankAlive[side][1] || TankGame::field->ActionIsValid(side, 1, act1)))
                    {
                        TankGame::field->nextAction[side][0] = act0;
                        TankGame::field->nextAction[side][1] = act1;
                        continue;
                    }
                }
                invalid[side] = true;
                output["display"]["loseReason"][side] = "INVALID_INPUT_VERDICT_" + raw["verdict"].asString();
            }
            if (invalid[0] || invalid[1])
            {
                output["command"] = "finish";
                if (invalid[0] == invalid[1])
                    setWinner(-1);
                else if (invalid[0])
                    setWinner(1);
                else
                    setWinner(0);
                break;
            }
            else
                TankGame::field->DoAction();

            int result = TankGame::field->GetGameResult();
            if (result != -2)
            {
                output["command"] = "finish";
                setWinner(result);
                for (int side = 0; side < TankGame::sideCount; side++)
                {
                    bool tankExist = TankGame::field->tankAlive[side][0] || TankGame::field->tankAlive[side][1];
                    bool baseExist = TankGame::field->baseAlive[side];
                    if (!tankExist && !baseExist)
                        output["display"]["loseReason"][side] = "BASE_TANK_ALL_DESTROYED";
                    else if (!tankExist)
                        output["display"]["loseReason"][side] = "TANK_ALL_DESTROYED";
                    else if (!baseExist)
                        output["display"]["loseReason"][side] = "BASE_DESTROYED";
                }
                break;
            }
            else if (isLast)
                output["command"] = "request";
            TankGame::field->DebugPrint();
        }
    }

    Json::FastWriter writer;
    cout << writer.write(output);
}