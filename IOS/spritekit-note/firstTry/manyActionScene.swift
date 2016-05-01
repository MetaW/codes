//
//  manyActionScene.swift
//  firstTry
//
//  Created by wanglulu on 15/12/5.
//  Copyright © 2015年 wanglulu. All rights reserved.
//

/*****************************************************
!!!!!sprite,场景，屏幕显示原理:!!!!!
1.  Sprite的大小是像素，默认大小为材质的分辨率，它的大小是绝对的，
    至于如何显示到屏幕规则如下：
    场景大小也是像素，他决定了Sprite组成的世界中可显示的最大区域，
    屏幕的分辨率并不决定显示区域，决定显示区域的是屏幕长宽比;
    根据屏幕长宽比，从场景正中心开始按照此长宽比找一个在场景之内的最大矩形，
    该矩形一定有两边与场景边缘重合，如果屏幕长宽比与场景长宽比一样，该矩形就与
    场景完全重合。
    该矩形之中的内容就是将要显示到屏幕上的内容，该矩形中的内容与屏幕的长宽比一致
    能够完全映射到屏幕上去，以上就是现实过程。

2.  实际能显示多少内容只与场景的大小和屏幕长宽比有关，为了使高分辨率屏幕
    显示的也比较清晰可以让场景大一些，尽量与分辨率最高的设备接近(推荐)，
    也可以根据设备屏幕在代码中改变场景大小。场景的长宽比尽量与不同设备的长宽比
    接近。

3.  此外也可以在代码中改变场景大小实现camera放大缩小效果。



########SKAction的创建和使用########

runAction的三种重载的用法：
1.  直接执行
2.  赋予对应键值后再执行，之后可随时通过键值来停止它
3.  直接执行，执行完之后回调一个匿名函数

SKAction的其他注意：
1.  someSprite.removeAllAction()方法会去除所以动作，一般用于某物体
    的状态突然改变，如挂掉了。

2.  !!!SKAction另一个非常重要的创建方法!!!
    eg:
    let myAction = SKAction.runBlock{
        print("可以实现任何自定义的事件动作")
    }

3.  等待事件，通常用于在构造序列事件时分开两个事件
    let waits = SKAction.waitForDuration(0.5)
    let actions = SKAction.sequence([actionA, waits, actionB])
    此时actionA执行完之后等待0.5秒才会执行actionsB

******************************************************/

import Foundation
import SpriteKit

class manyActionScene:SKScene
{
    let bird = SKSpriteNode()
    var flyAction = SKAction()
    
    override func didMoveToView(view: SKView) {
        self.size = CGSize(width: 1024, height: 800)
        
        bird.texture = SKTexture(imageNamed: "fly1.png")
        bird.size = CGSize(width: 105,height: 85)
        bird.position = CGPointMake(self.size.width/2, self.size.height/2 + 50)
        self.addChild(bird)
        
        //
        let leftPath = SKAction.moveByX(-200, y: -10, duration: 2)
        let rightPath = SKAction.moveByX(200, y: 10, duration: 2)
        let flipNegative = SKAction.scaleXTo(-1, duration: 0)
        let flipPositive = SKAction.scaleXTo(1, duration: 0)
        
        //
        //SKAction.group(actions: [SKAction])
        let move = SKAction.sequence([leftPath, flipNegative, rightPath, flipPositive])
        let alwaysMove = SKAction.repeatActionForever(move)
        
        bird.runAction(alwaysMove)
        
        //
        let unreal = SKAction.fadeAlphaTo(0.5, duration: 0.3)
        let real = SKAction.fadeAlphaTo(1, duration: 0.3)
        let realToUnreal = SKAction.sequence([real, unreal])
        let continueChange = SKAction.repeatActionForever(realToUnreal)
        
        bird.runAction(continueChange)
        
        //
        //-----------------------------
        let birdAtlas = SKTextureAtlas(named: "fly.atlas")
        let birdFrame:[SKTexture] = [
            birdAtlas.textureNamed("fly1.png"),
            birdAtlas.textureNamed("fly2.png")]
        //
        let fAction = SKAction.animateWithTextures(birdFrame, timePerFrame: 0.14)
        
        //
        flyAction = SKAction.repeatActionForever(fAction)
        //另一个方法可以指定重复次数
        //flyAction = SKAction.repeatAction(fAction, count: 5)
    }
    
    override func touchesBegan(touches: Set<UITouch>, withEvent event: UIEvent?) {
        
        for _ in touches{
            
            self.size = CGSize(width: 800, height: 600)
            
            //
            bird.runAction(flyAction, withKey: "fly")
        }
    }
    
    override func touchesEnded(touches: Set<UITouch>, withEvent event: UIEvent?) {
        for _ in touches
        {
            self.size = CGSize(width: 1024, height: 800)
            
            //
            bird.removeActionForKey("fly")
        }
    }
    
    
}

