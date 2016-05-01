//
//  MenuScene.swift
//  firstTry
//
//  Created by wanglulu on 15/12/11.
//  Copyright © 2015年 wanglulu. All rights reserved.
//
/***************************************************
本Demo包含：
1.  menu菜单的示例

2.  anchorPoint的讲解

3.  SKLabelNode的使用

4.  在touch事件中确定被touch的对象

5.  场景的切换

****************************************************/
import Foundation
import SpriteKit

class MenuScene:SKScene {
    
    var play = SKLabelNode()
    
    override func didMoveToView(view: SKView) {
    
        self.size = CGSize(width: 1100, height: 700)
        
        //任何一个SKNode都有一个anchorPoint属性,其值为(0,0)至(1,1)
        //(0,0)代表左下角,(1,1)代表右上角,(1,0)代表右下角。。。
        //当该node作为父节点时，anchorPoint代表该node的坐标原点在何处
        //当该node作为子节点时，anchorPoint代表该node的定位点在何处
        //默认情况下scene的anchorPoint为(0,0),SKSpriteNode的为(0.5,0.5)
        //这里将scene的anchorPoint设为(0.5,0.5)是为了方便,因为这样坐标原点就在scene的中心
        self.anchorPoint = CGPoint(x: 0.5, y: 0.5)
        
        self.backgroundColor = UIColor.purpleColor()
        
        //SKLabelNode的使用例子，除了设定字体，字大小，内容之外，与其他Sprite完全一样
        let logo = SKLabelNode(fontNamed: "AvenirNext-Heavy")
        logo.text = "WOOO! It's amazing!"
        logo.position = CGPoint(x: 0, y: 200)
        logo.fontSize = 80
        self.addChild(logo)
        
        play = SKLabelNode(fontNamed: "AvenirNext-HeavyItalic")
        play.text = "PLAY!"
        play.position = CGPoint(x: 0, y: -50)
        play.fontColor = UIColor.yellowColor()
        play.fontSize = 120
        
        //每一个SKNode对象都由一个name属性，可以为其赋值，方便后面的找对象工作，类似于UIkit中的tag
        play.name = "buttonPlay"
        self.addChild(play)
        
        let act1 = SKAction.scaleTo(0.85, duration: 0.85)
        let act2 = SKAction.scaleTo(1, duration: 0.85)
        let act3 = SKAction.sequence([act1, act2])
        let act = SKAction.repeatActionForever(act3)
        play.runAction(act)
    }
    
    override func touchesBegan(touches: Set<UITouch>, withEvent event: UIEvent?) {
        for touch in touches{
            let posi = touch.locationInNode(self)
            let nodeTouched = nodeAtPoint(posi)
            
            let act = SKAction.scaleTo(0.5, duration: 1)
            self.play.runAction(act)
            
            //nodeTouched.name的返回值是一个可选型，不能与"buttonPlay"直接比较，要先
            //进行解包操作，通常可用"!"或"if let"语句将一个可选型转为一般类型
            if nodeTouched.name! == "buttonPlay"
            {
                let scene = GameScene(fileNamed: "GameScene.sks")
                
                //!!!!!!一定要先创建scene再设置好scaleMode属性之后才显示它，否则
                //先显示再在scene中设置scaleMode，设置不会有效果!!!
                scene?.scaleMode = .AspectFill
                
                //通过self(scene)也能访问到其父节点SKView并调用它的presentScene来切换场景
                self.view?.presentScene(scene!,transition:SKTransition.crossFadeWithDuration(2))
            }
        }
    }
    
}